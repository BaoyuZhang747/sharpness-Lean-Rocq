import Sharpness.Unconditional.FiniteGroupFusionExtensionMap

/-! Sylow conjugacy corrects the conjugating element by an element centralizing
the target subgroup, yielding an extension on the exact fusion extension domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G] [Finite G]

theorem finiteGroupExtension_correction (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    {P Q : Subgroup S} (hQ : (finiteGroupFusion (S : Subgroup G)).FullyNormalized Q)
    (e : P ≃* Q) (g : G)
    (hg : ∀ x : P, ((e x).val : G) = g * (x.val : G) * g⁻¹) :
    ∃ c : G, (∀ y : Q, c * (y.val : G) * c⁻¹ = (y.val : G)) ∧
      ∀ n : (finiteGroupFusion (S : Subgroup G)).extensionDomainSubgroup e,
        (c*g) * (n.val : G) * (c*g)⁻¹ ∈ (S : Subgroup G) := by
  let K := finiteGroupNormalizerPreimage (S : Subgroup G) Q
  let T : Sylow p K := (finiteGroupNormalizerSylow p S Q hQ).subtype
    (finiteGroupNormalizerSubgroup_le_preimage (S : Subgroup G) Q)
  let f := finiteGroupExtensionConjugation (S : Subgroup G) e g hg
  have hH : IsPGroup p f.range :=
    (S.isPGroup'.to_subgroup
      ((finiteGroupFusion (S : Subgroup G)).extensionDomainSubgroup e)).of_surjective
        f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := finiteGroup_pSubgroup_conjugates_into p T f.range hH
  obtain ⟨t, ht⟩ := k.property
  let c : G := (t.val : G)⁻¹ * k.val.val
  refine ⟨c, ?_, ?_⟩
  · intro y
    have ha := congrArg (fun a : MulAut Q => ((a y).val : G)) ht
    rw [finiteGroupNormalizerAction_apply] at ha
    change (t.val : G) * (y.val : G) * (t.val : G)⁻¹ =
      k.val.val * (y.val : G) * k.val.val⁻¹ at ha
    calc
      c * (y.val : G) * c⁻¹ =
          (t.val : G)⁻¹ * (k.val.val * (y.val : G) * k.val.val⁻¹) * (t.val : G) := by
        dsimp [c]
        group
      _ = (y.val : G) := by rw [← ha]; group
  · intro n
    have hn : k * f n * k⁻¹ ∈ (T : Subgroup K) :=
      hk ⟨f n, ⟨n, rfl⟩, rfl⟩
    have hn' : k.val.val * (g * (n.val : G) * g⁻¹) * k.val.val⁻¹ ∈ (S : Subgroup G) := hn
    have hm := (S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem t.val.property) hn')
      t.val.property
    convert hm using 1 <;> dsimp [c] <;> group

theorem finiteGroupFusion_fullyNormalized_receptive (p : ℕ) [Fact p.Prime]
    (S : Sylow p G) (Q : Subgroup S)
    (hQ : (finiteGroupFusion (S : Subgroup G)).FullyNormalized Q) :
    (finiteGroupFusion (S : Subgroup G)).Receptive Q := by
  intro P e he
  obtain ⟨g, hg⟩ := he
  obtain ⟨c, hc, hmem⟩ := finiteGroupExtension_correction p S hQ e g hg
  let f : (finiteGroupFusion (S : Subgroup G)).extensionDomainSubgroup e →*
      (⊤ : Subgroup S) :=
    { toFun n := ⟨⟨(c*g) * (n.val : G) * (c*g)⁻¹, hmem n⟩, trivial⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' x y := by apply Subtype.ext; apply Subtype.ext; simp [mul_assoc] }
  refine ⟨f, ⟨c*g, fun _ => rfl⟩, ?_⟩
  intro x
  apply Subtype.ext
  change (c*g) * (x.val : G) * (c*g)⁻¹ = ((e x).val : G)
  calc
    _ = c * (g * (x.val : G) * g⁻¹) * c⁻¹ := by group
    _ = _ := by rw [← hg x]; exact hc (e x)

end Sharpness
