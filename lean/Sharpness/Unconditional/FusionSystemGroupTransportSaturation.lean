import Sharpness.Unconditional.FusionSystemGroupTransportExtension

/-! Both saturation axioms are preserved by genuine group equivalences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v
namespace Sharpness.FusionSystem
variable {S : Type u} {T : Type v} [Group S] [Group T] [Finite S] [Finite T]
variable (F : FusionSystem T) (e : S ≃* T)

theorem groupTransport_saturated (p : ℕ) (sat : F.Saturated p) :
    (F.groupTransport e).Saturated p where
  fully_normalized P hP := by
    obtain ⟨hc, hi⟩ := sat.fully_normalized (P.map e.toMonoidHom)
      ((F.groupTransport_fullyNormalized_iff e P).mp hP)
    refine ⟨(F.groupTransport_fullyCentralized_iff e P).mpr hc, ?_⟩
    rwa [F.groupTransport_automorphism_relIndex e P]
  extension {P Q} a ha hQ := by
    obtain ⟨N, hPN, hN, f, hf, hext⟩ := sat.extension (groupTransportEquiv e a) ha
      ((F.groupTransport_fullyCentralized_iff e Q).mp hQ)
    let N₀ := N.comap e.toMonoidHom
    have hPN₀ : P ≤ N₀ := fun x hx => hPN ⟨x, hx, rfl⟩
    have hN₀ : (N₀ : Set S) = (F.groupTransport e).extensionDomain a := by
      ext s
      change e s ∈ N ↔ s ∈ (F.groupTransport e).extensionDomain a
      rw [show e s ∈ N ↔ e s ∈ F.extensionDomain (groupTransportEquiv e a) from
        Set.ext_iff.mp hN (e s)]
      exact (F.groupTransport_extensionDomain_iff e a s).symm
    let j : N₀ →* N := (e.toMonoidHom.comp N₀.subtype).codRestrict N (fun n => n.property)
    let f₀ : N₀ →* (⊤ : Subgroup S) :=
      (e.symm.toMonoidHom.comp ((⊤ : Subgroup T).subtype.comp (f.comp j))).codRestrict ⊤
        (fun _ => trivial)
    have hmap : N₀.map e.toMonoidHom ≤ N := Subgroup.map_comap_le _ _
    let g := f.comp (subgroupInclusion _ _ hmap)
    have hg : F.IsHom g := F.comp_mem _ _ (F.inclusion_mem hmap) hf
    have hf₀ : (F.groupTransport e).IsHom f₀ := by
      apply F.codomain_restrict_mem g hg le_top (groupTransportHom e f₀)
      ext x
      change e (e.symm (f ⟨e (e.symm x.val), _⟩).val) = (f ⟨x.val, _⟩).val
      simp
    refine ⟨N₀, hPN₀, hN₀, f₀, hf₀, ?_⟩
    intro x
    apply e.injective
    change e (e.symm (f ⟨e x.val, _⟩).val) = e (a x).val
    rw [e.apply_symm_apply]
    simpa only [groupTransportEquiv_apply, MulEquiv.coe_subgroupMap_apply] using
      hext (e.subgroupMap P x)

end Sharpness.FusionSystem
