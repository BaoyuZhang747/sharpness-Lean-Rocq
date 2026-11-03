import Sharpness.FusionMackey

/-! Actual subgroup images and orbit functors for a subsystem over T ≤ S.
The subsystem condition only says its actual homomorphisms belong to F;
it contains no Mackey-restriction or higher-limit conclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {S : Type u} [Group S] (T : Subgroup S)

abbrev ambientSubgroup (P : Subgroup T) : Subgroup S := P.map T.subtype

def subgroupAmbientEquiv (P : Subgroup T) : P ≃* ambientSubgroup T P :=
  P.equivMapOfInjective T.subtype Subtype.val_injective

theorem subgroupAmbientEquiv_val (P : Subgroup T) (x : P) :
    (subgroupAmbientEquiv T P x).val = x.val.val := rfl

theorem subgroupAmbientEquiv_symm_val (P : Subgroup T) (x : ambientSubgroup T P) :
    ((subgroupAmbientEquiv T P).symm x).val.val = x.val :=
  congrArg (fun y : ambientSubgroup T P => y.val) ((subgroupAmbientEquiv T P).apply_symm_apply x)

def ambientHom {P Q : Subgroup T} (f : P →* Q) : ambientSubgroup T P →* ambientSubgroup T Q :=
  (subgroupAmbientEquiv T Q).toMonoidHom.comp (f.comp (subgroupAmbientEquiv T P).symm.toMonoidHom)

theorem ambientHom_apply {P Q : Subgroup T} (f : P →* Q) (x : P) :
    ambientHom T f (subgroupAmbientEquiv T P x) = subgroupAmbientEquiv T Q (f x) := by
  change subgroupAmbientEquiv T Q (f ((subgroupAmbientEquiv T P).symm (subgroupAmbientEquiv T P x))) = _
  rw [MulEquiv.symm_apply_apply]

theorem ambientHom_id (P : Subgroup T) : ambientHom T (MonoidHom.id P) =
    MonoidHom.id (ambientSubgroup T P) := by
  apply MonoidHom.ext
  intro x
  exact (subgroupAmbientEquiv T P).apply_symm_apply x

theorem ambientHom_comp {P Q R : Subgroup T} (f : P →* Q) (g : Q →* R) :
    ambientHom T (g.comp f) = (ambientHom T g).comp (ambientHom T f) := by
  apply MonoidHom.ext
  intro x
  change subgroupAmbientEquiv T R (g (f ((subgroupAmbientEquiv T P).symm x))) =
    subgroupAmbientEquiv T R (g ((subgroupAmbientEquiv T Q).symm
      (subgroupAmbientEquiv T Q (f ((subgroupAmbientEquiv T P).symm x)))))
  rw [MulEquiv.symm_apply_apply]

namespace FusionSystem
variable (F : FusionSystem S) (H : FusionSystem T)

structure SubsystemEmbedding : Prop where
  hom_mem : ∀ {P Q : Subgroup T} (f : P →* Q), H.IsHom f → F.IsHom (ambientHom T f)

variable (h : F.SubsystemEmbedding T H)

def subsystemRawFunctor : H.Object ⥤ F.Object where
  obj P := ⟨ambientSubgroup T P.subgroup⟩
  map f := ⟨ambientHom T f.val, h.hom_mem f.val f.property⟩
  map_id P := by
    apply Subtype.ext
    exact ambientHom_id T P.subgroup
  map_comp f g := by
    apply Subtype.ext
    exact ambientHom_comp T f.val g.val

theorem subsystemRaw_respects_inner {P Q : H.Object} (f g : P ⟶ Q)
    (related : H.targetInner f g) :
    (F.subsystemRawFunctor T H h ⋙ F.toOrbit).map f =
      (F.subsystemRawFunctor T H h ⋙ F.toOrbit).map g := by
  apply (F.orbit_map_eq_iff _ _).mpr
  obtain ⟨r, hr⟩ := related
  refine ⟨subgroupAmbientEquiv T Q.subgroup r, ?_⟩
  intro x
  obtain ⟨x₀, rfl⟩ := (subgroupAmbientEquiv T P.subgroup).surjective x
  change ambientHom T g.val (subgroupAmbientEquiv T P.subgroup x₀) =
    (subgroupAmbientEquiv T Q.subgroup r)⁻¹ *
      ambientHom T f.val (subgroupAmbientEquiv T P.subgroup x₀) * subgroupAmbientEquiv T Q.subgroup r
  rw [ambientHom_apply, ambientHom_apply, hr x₀, map_mul, map_mul, map_inv]

def subsystemOrbitFunctor : H.Orbit ⥤ F.Orbit :=
  CategoryTheory.Quotient.lift H.targetInner (F.subsystemRawFunctor T H h ⋙ F.toOrbit)
    (fun _ _ f g r => F.subsystemRaw_respects_inner T H h f g r)

theorem subsystemOrbitFunctor_map_raw {P Q : H.Object} (f : P ⟶ Q) :
    (F.subsystemOrbitFunctor T H h).map (H.toOrbit.map f) =
      F.toOrbit.map ((F.subsystemRawFunctor T H h).map f) := rfl

end FusionSystem
end Sharpness
