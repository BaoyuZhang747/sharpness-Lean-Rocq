import Sharpness.SubsystemEmbedding
import Sharpness.SpanEquations
import Sharpness.SubgroupEqualityIso

/-! The image of a subsystem intersection span is the actual ambient
intersection span, with explicit apex isomorphism and both arrow squares. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S) (T : Subgroup S)
    (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    {P Q R : H.Object} (f : P ⟶ R) (g : Q ⟶ R) (u : R.subgroup)

abbrev subsystemSpanApex := F.spanApex ((F.subsystemRawFunctor T H h).map f)
  ((F.subsystemRawFunctor T H h).map g) (subgroupAmbientEquiv T R.subgroup u)

theorem subsystem_span_subgroup_eq : ambientSubgroup T (H.spanApex f g u).subgroup =
    (F.subsystemSpanApex T H h f g u).subgroup := by
  ext x
  constructor
  · rintro ⟨xT, hxT, rfl⟩
    obtain ⟨a, ha, b, hb⟩ := (H.mem_spanApex_iff f g u xT).mp hxT
    apply (F.mem_spanApex_iff _ _ _ _).mpr
    refine ⟨subgroupAmbientEquiv T P.subgroup a, congrArg (fun t : T => t.val) ha,
      subgroupAmbientEquiv T Q.subgroup b, ?_⟩
    change ambientHom T g.val (subgroupAmbientEquiv T Q.subgroup b) =
      (subgroupAmbientEquiv T R.subgroup u)⁻¹ *
        ambientHom T f.val (subgroupAmbientEquiv T P.subgroup a) * subgroupAmbientEquiv T R.subgroup u
    rw [ambientHom_apply, ambientHom_apply, hb, map_mul, map_mul, map_inv]
  · intro hx
    obtain ⟨a', ha, b', hb⟩ := (F.mem_spanApex_iff _ _ _ x).mp hx
    obtain ⟨a, rfl⟩ := (subgroupAmbientEquiv T P.subgroup).surjective a'
    obtain ⟨b, rfl⟩ := (subgroupAmbientEquiv T Q.subgroup).surjective b'
    have hold : g.val b = u⁻¹ * f.val a * u := by
      apply (subgroupAmbientEquiv T R.subgroup).injective
      change ambientHom T g.val (subgroupAmbientEquiv T Q.subgroup b) =
        (subgroupAmbientEquiv T R.subgroup u)⁻¹ *
          ambientHom T f.val (subgroupAmbientEquiv T P.subgroup a) * subgroupAmbientEquiv T R.subgroup u at hb
      rw [ambientHom_apply, ambientHom_apply] at hb
      simpa only [map_mul, map_inv] using hb
    refine ⟨a.val, ?_, ha⟩
    exact (H.mem_spanApex_iff f g u a.val).mpr ⟨a, rfl, b, hold⟩

def subsystemSpanIso : (F.subsystemRawFunctor T H h).obj (H.spanApex f g u) ≅
    F.subsystemSpanApex T H h f g u :=
  F.subgroupEqualityIso (F.subsystem_span_subgroup_eq T H h f g u)

theorem subsystemSpan_left_square :
    (F.subsystemRawFunctor T H h).map (H.spanLeft f g u) =
      (F.subsystemSpanIso T H h f g u).hom ≫
        F.spanLeft ((F.subsystemRawFunctor T H h).map f) ((F.subsystemRawFunctor T H h).map g)
          (subgroupAmbientEquiv T R.subgroup u) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  obtain ⟨x₀, rfl⟩ := (subgroupAmbientEquiv T (H.spanApex f g u).subgroup).surjective x
  apply Subtype.ext
  change (ambientHom T (H.spanLeft f g u).val
    (subgroupAmbientEquiv T (H.spanApex f g u).subgroup x₀)).val =
      (subgroupAmbientEquiv T (H.spanApex f g u).subgroup x₀).val
  rw [ambientHom_apply]
  rfl

theorem subsystemSpan_right_square :
    (F.subsystemRawFunctor T H h).map (H.concreteSpan f g u).right =
      (F.subsystemSpanIso T H h f g u).hom ≫
        (F.concreteSpan ((F.subsystemRawFunctor T H h).map f) ((F.subsystemRawFunctor T H h).map g)
          (subgroupAmbientEquiv T R.subgroup u)).right := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  obtain ⟨x₀, rfl⟩ := (subgroupAmbientEquiv T (H.spanApex f g u).subgroup).surjective x
  apply F.injective ((F.subsystemRawFunctor T H h).map g).val
    ((F.subsystemRawFunctor T H h).map g).property
  let xF := (F.subsystemSpanIso T H h f g u).hom.val
    (subgroupAmbientEquiv T (H.spanApex f g u).subgroup x₀)
  have hl : (F.spanLeft ((F.subsystemRawFunctor T H h).map f)
        ((F.subsystemRawFunctor T H h).map g) (subgroupAmbientEquiv T R.subgroup u)).val xF =
      subgroupAmbientEquiv T P.subgroup ((H.spanLeft f g u).val x₀) := by
    have hp := congrArg (fun t => t.val (subgroupAmbientEquiv T (H.spanApex f g u).subgroup x₀))
      (F.subsystemSpan_left_square T H h f g u)
    exact hp.symm.trans (ambientHom_apply T (H.spanLeft f g u).val x₀)
  have hf := (congrArg ((F.subsystemRawFunctor T H h).map f).val hl).trans
    (ambientHom_apply T f.val ((H.spanLeft f g u).val x₀))
  have hm := congrArg (fun t => (subgroupAmbientEquiv T R.subgroup u)⁻¹ * t *
    subgroupAmbientEquiv T R.subgroup u) hf
  have hconj : subgroupAmbientEquiv T R.subgroup (u⁻¹ * f.val ((H.spanLeft f g u).val x₀) * u) =
      (subgroupAmbientEquiv T R.subgroup u)⁻¹ *
        subgroupAmbientEquiv T R.subgroup (f.val ((H.spanLeft f g u).val x₀)) *
          subgroupAmbientEquiv T R.subgroup u := by rw [map_mul, map_mul, map_inv]
  have hold := congrArg (subgroupAmbientEquiv T R.subgroup) (H.concreteSpan_right_equation f g u x₀)
  have htarget := F.concreteSpan_right_equation ((F.subsystemRawFunctor T H h).map f)
    ((F.subsystemRawFunctor T H h).map g) (subgroupAmbientEquiv T R.subgroup u) xF
  have hleft := (congrArg (ambientHom T g.val)
    (ambientHom_apply T (H.concreteSpan f g u).right.val x₀)).trans
      (ambientHom_apply T g.val ((H.concreteSpan f g u).right.val x₀))
  exact hleft.trans (hold.trans (hconj.trans (hm.symm.trans htarget.symm)))

end Sharpness.FusionSystem
