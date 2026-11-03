import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalConjugation

/-! The local extension predicate agrees with literal equality of subgroup
images, with no unproved preservation or invertibility condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricChain
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}

omit [Finite S] in
theorem normalizerExtension_allowed (σ : F.CentricChain) {P Q : Subgroup S}
    (f : P →* Q) (hf : σ.NormalizerExtension f) : F.IsHom f := by
  obtain ⟨a, b, hb, ha, hf⟩ := hf
  apply F.codomain_restrict_mem
    (b.comp (subgroupInclusion P (σ.topSubgroup ⊔ P) le_sup_right))
    (F.comp_mem _ _ (F.inclusion_mem _) hb) le_sup_right f
  apply MonoidHom.ext
  intro x
  exact Subtype.ext (hf x).symm

/-- The point-set image formulation of preserving the chain. -/
def NormalizerExtensionImages (σ : F.CentricChain) {P Q : Subgroup S} (f : P →* Q) : Prop :=
  ∃ b : (σ.topSubgroup ⊔ P : Subgroup S) →* (σ.topSubgroup ⊔ Q : Subgroup S),
    F.IsHom b ∧
    (∀ i, (fun x : (σ.topSubgroup ⊔ P : Subgroup S) => (b x).val) ''
      {x | x.val ∈ σ.subgroup i} = (σ.subgroup i : Set S)) ∧
    (∀ x : P, (b ⟨x.val, Subgroup.mem_sup_right x.property⟩).val = (f x).val)

theorem normalizerExtension_iff_images (σ : F.CentricChain) {P Q : Subgroup S}
    (f : P →* Q) : σ.NormalizerExtension f ↔ σ.NormalizerExtensionImages f := by
  constructor
  · rintro ⟨a, b, hb, htop, hf⟩
    refine ⟨b, hb, fun i => ?_, hf⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxt := σ.subgroup_mono (Fin.le_last i) hx
      have he := htop ⟨x.val, hxt⟩
      change (b x).val = _ at he
      change (b x).val ∈ σ.subgroup i
      rw [he]
      exact (a.property i ⟨x.val, hxt⟩).mp hx
    · intro hy
      let yT : σ.topSubgroup := ⟨y, σ.subgroup_mono (Fin.le_last i) hy⟩
      let x := a.val.val.symm yT
      have hx : x.val ∈ σ.subgroup i := by
        apply (a.property i x).mpr
        change (a.val.val (a.val.val.symm yT)).val ∈ σ.subgroup i
        rw [a.val.val.apply_symm_apply]
        exact hy
      refine ⟨⟨x.val, Subgroup.mem_sup_left x.property⟩, hx, ?_⟩
      exact (htop x).trans (congrArg Subtype.val (a.val.val.apply_symm_apply yT))
  · rintro ⟨b, hb, images, hf⟩
    have ht (x : σ.topSubgroup) :
        (b ⟨x.val, Subgroup.mem_sup_left x.property⟩).val ∈ σ.topSubgroup := by
      change _ ∈ (σ.subgroup (Fin.last σ.length) : Set S)
      rw [← images (Fin.last σ.length)]
      exact ⟨⟨x.val, Subgroup.mem_sup_left x.property⟩, x.property, rfl⟩
    let c : σ.topSubgroup →* σ.topSubgroup :=
      { toFun x := ⟨(b ⟨x.val, Subgroup.mem_sup_left x.property⟩).val, ht x⟩
        map_one' := by apply Subtype.ext; exact congrArg (fun z : (σ.topSubgroup ⊔ Q : Subgroup S) => z.val) b.map_one
        map_mul' x y := by
          apply Subtype.ext
          exact congrArg (fun z : (σ.topSubgroup ⊔ Q : Subgroup S) => z.val) (b.map_mul
            ⟨x.val, Subgroup.mem_sup_left x.property⟩
            ⟨y.val, Subgroup.mem_sup_left y.property⟩) }
    have hc : F.IsHom c := by
      apply F.codomain_restrict_mem
        (b.comp (subgroupInclusion σ.topSubgroup (σ.topSubgroup ⊔ P) le_sup_left))
        (F.comp_mem _ _ (F.inclusion_mem _) hb) le_sup_left c
      rfl
    have hcs : Function.Surjective c := by
      intro y
      have hy : y.val ∈ (σ.subgroup (Fin.last σ.length) : Set S) := y.property
      rw [← images (Fin.last σ.length)] at hy
      obtain ⟨x, hx, he⟩ := hy
      exact ⟨⟨x.val, hx⟩, Subtype.ext he⟩
    let e := MulEquiv.ofBijective c ⟨F.injective c hc, hcs⟩
    have hpres : (⟨e, hc⟩ : F.automorphismSubgroup σ.topSubgroup) ∈ σ.fusionStabilizer := by
      intro i x
      constructor
      · intro hx
        change (b ⟨x.val, Subgroup.mem_sup_left x.property⟩).val ∈ (σ.subgroup i : Set S)
        rw [← images i]
        exact ⟨⟨x.val, Subgroup.mem_sup_left x.property⟩, hx, rfl⟩
      · intro hx
        change (b ⟨x.val, Subgroup.mem_sup_left x.property⟩).val ∈ (σ.subgroup i : Set S) at hx
        rw [← images i] at hx
        obtain ⟨y, hy, he⟩ := hx
        have heq : y = ⟨x.val, Subgroup.mem_sup_left x.property⟩ :=
          F.injective b hb (Subtype.ext he)
        change y.val ∈ σ.subgroup i at hy
        simpa only [heq] using hy
    exact ⟨⟨⟨e, hc⟩, hpres⟩, b, hb, fun _ => rfl, hf⟩

end Sharpness.FusionSystem.CentricChain


