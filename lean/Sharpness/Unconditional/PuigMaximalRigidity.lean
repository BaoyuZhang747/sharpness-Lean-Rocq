import Sharpness.Unconditional.PuigMaximalSpans
import Sharpness.Unconditional.FusionAtomicExtension

/-! The simultaneous stabilizer of the two projections of a maximal
centric span is trivial. A stabilizing normalizer element gives a larger
span by saturation, and maximality forces it into the original subgroup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- A maximal span whose first leg is inclusion has no nontrivial
automorphism fixing both legs. -/
theorem maximal_normalized_span_aut_eq_one (p : ℕ) (sat : F.Saturated p)
    {A : Subgroup S} (hA : F.IsCentric A) {P T : F.CentricOrbit}
    (hAP : A ≤ P.obj.as.subgroup) (β : F.toOrbit.obj ⟨A⟩ ⟶ T.obj)
    (hmax : (show PuigSpan P T from
      { apex := ⟨F.toOrbit.obj ⟨A⟩, hA⟩
        left := ObjectProperty.homMk (F.toOrbit.map (F.inclusion hAP))
        right := ObjectProperty.homMk β }).Maximal)
    (a : Aut (F.toOrbit.obj ⟨A⟩))
    (haP : a.hom ≫ F.toOrbit.map (F.inclusion hAP) = F.toOrbit.map (F.inclusion hAP))
    (haβ : a.hom ≫ β = β) : a = 1 := by
  let H := F.orbitHomStabilizer β
  let K := F.atomicNormalizerPreimage A H ⊓ P.obj.as.subgroup
  have hAK : A ≤ K := le_inf (F.le_atomicNormalizerPreimage A H) hAP
  have hKP : K ≤ P.obj.as.subgroup := inf_le_right
  have hKN : K ≤ Subgroup.normalizer (A : Set S) :=
    inf_le_left.trans (F.atomicNormalizerPreimage_le_normalizer A H)
  let β₀ := F.orbitRepresentative β
  have hw : ∀ n : K, ∃ t : T.obj.as.subgroup, ∀ x : A,
      (β₀.val (A.normalizerMonoidHom ⟨n.val, hKN n.property⟩ x)).val =
        t.val * (β₀.val x).val * t.val⁻¹ := by
    intro n
    apply F.fixed_normalizer_has_target_witness β₀ ⟨n.val, hKN n.property⟩
    rw [F.orbitRepresentative_map]
    exact ((F.mem_atomicNormalizerPreimage A H n.val).mp n.property.1).choose_spec
  obtain ⟨g, hg, hext⟩ := F.centric_normalizer_extension p sat hAK hKN hA β₀ hw
  let g₀ : (⟨K⟩ : F.Object) ⟶ T.obj.as := ⟨g, hg⟩
  have hraw : F.inclusion hAK ≫ g₀ = β₀ := by
    apply Subtype.ext
    ext x
    exact hext x
  let B : PuigSpan P T :=
    { apex := ⟨F.toOrbit.obj ⟨K⟩, F.centric_overgroup hA hAK⟩
      left := ObjectProperty.homMk (F.toOrbit.map (F.inclusion hKP))
      right := ObjectProperty.homMk (F.toOrbit.map g₀) }
  let t : (show PuigSpan P T from
      { apex := ⟨F.toOrbit.obj ⟨A⟩, hA⟩
        left := ObjectProperty.homMk (F.toOrbit.map (F.inclusion hAP))
        right := ObjectProperty.homMk β }).Factor B :=
    { hom := ObjectProperty.homMk (F.toOrbit.map (F.inclusion hAK))
      left_fac := by
        apply ObjectProperty.hom_ext
        change F.toOrbit.map (F.inclusion hAK) ≫ F.toOrbit.map (F.inclusion hKP) = _
        rw [← F.toOrbit.map_comp]
        rfl
      right_fac := by
        apply ObjectProperty.hom_ext
        change F.toOrbit.map (F.inclusion hAK) ≫ F.toOrbit.map g₀ = β
        rw [← F.toOrbit.map_comp, hraw, F.orbitRepresentative_map] }
  letI : IsIso t.hom := hmax B t
  have hKA : K = A := (Subgroup.eq_of_le_of_card_ge hAK
    (F.orbitOrder_mono (inv t.hom.hom))).symm
  have ha : a ∈ (F.relativeNormalizerToAut P.obj.as.subgroup A).range := by
    rw [F.relativeNormalizerToAut_range hAP]
    exact haP
  obtain ⟨n, hn⟩ := ha
  have hnK : n.val ∈ K := by
    refine ⟨(F.mem_atomicNormalizerPreimage A H n.val).mpr ⟨n.property.1, ?_⟩, n.property.2⟩
    change F.relativeNormalizerToAut P.obj.as.subgroup A n ∈ H
    rw [hn]
    exact haβ
  have hnA : n.val ∈ A := (le_of_eq hKA) hnK
  exact hn.symm.trans (F.subgroup_killed_by_normalizerAut P.obj.as.subgroup A hnA)

end Sharpness.FusionSystem
