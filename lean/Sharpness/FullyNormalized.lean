import Sharpness.Saturation

/-! The fully-normalized conjugate and normal-p-subgroup Sylow steps in
manuscript Lemma 3.1, on the actual automorphism groups. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem exists_fullyNormalized (P : Subgroup S) :
    ∃ (Q : Subgroup S) (e : P ≃* Q), F.IsHom e.toMonoidHom ∧ F.FullyNormalized Q := by
  classical
  letI : Fintype (Subgroup S) := Fintype.ofFinite _
  let X := Finset.univ.filter (fun Q : Subgroup S => ∃ e : P ≃* Q, F.IsHom e.toMonoidHom)
  have hP : P ∈ X := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨MulEquiv.refl P, F.id_mem P⟩⟩
  obtain ⟨Q, hQ, maximal⟩ := X.exists_max_image
    (fun R : Subgroup S => Nat.card (Subgroup.normalizer (R : Set S))) ⟨P, hP⟩
  obtain ⟨e, he⟩ := (Finset.mem_filter.mp hQ).2
  refine ⟨Q, e, he, ?_⟩
  intro R a ha
  apply maximal R
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e.trans a, F.comp_mem _ _ he ha⟩⟩

theorem conjugation_isPGroup (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (P : Subgroup S) :
    IsPGroup p (F.innerSylowSubgroup P) :=
  (hS.to_subgroup (Subgroup.normalizer (P : Set S))).of_surjective
    P.normalizerMonoidHom.rangeRestrict P.normalizerMonoidHom.rangeRestrict_surjective

theorem normal_p_subgroup_le_conjugation (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (sat : F.Saturated p) (P : Subgroup S) (fully : F.FullyNormalized P)
    (N : Subgroup (F.automorphismSubgroup P)) [N.Normal] (hN : IsPGroup p N) :
    N ≤ (F.innerSylowSubgroup P).subgroupOf (F.automorphismSubgroup P) := by
  let H := (F.innerSylowSubgroup P).subgroupOf (F.automorphismSubgroup P)
  have hpH : IsPGroup p H :=
    (F.conjugation_isPGroup p hS P).of_equiv
      (Subgroup.subgroupOfEquivOfLe (F.innerSylowSubgroup_le P)).symm
  have index : ¬ p ∣ H.index := (sat.fully_normalized P fully).2
  exact hN.le_sylow_of_normal (hpH.toSylow index)

end Sharpness.FusionSystem
