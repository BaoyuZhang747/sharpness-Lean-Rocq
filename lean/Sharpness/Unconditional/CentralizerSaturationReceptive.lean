import Sharpness.Saturation

/-! The exact extension-domain subgroup and receptivity. These are general
fusion-system lemmas used in the centralizer and quotient saturation proofs. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- The subgroup with exactly the carrier specified by `extensionDomain`. -/
def extensionDomainSubgroup {P Q : Subgroup S} (e : P ≃* Q) : Subgroup S where
  carrier := F.extensionDomain e
  one_mem' := ⟨1, rfl, 1, by intro x; simp⟩
  mul_mem' {x y} hx hy := by
    obtain ⟨n, rfl, t, ht⟩ := hx
    obtain ⟨m, rfl, u, hu⟩ := hy
    refine ⟨n * m, rfl, t * u, ?_⟩
    intro x
    change e ((P.normalizerMonoidHom (n * m)) x) =
      (Q.normalizerMonoidHom (t * u)) (e x)
    rw [map_mul, map_mul]
    change e ((P.normalizerMonoidHom n) ((P.normalizerMonoidHom m) x)) =
      (Q.normalizerMonoidHom t) ((Q.normalizerMonoidHom u) (e x))
    rw [ht, hu]
  inv_mem' {x} hx := by
    obtain ⟨n, rfl, t, ht⟩ := hx
    refine ⟨n⁻¹, rfl, t⁻¹, ?_⟩
    intro x
    have h := ht ((P.normalizerMonoidHom n⁻¹) x)
    rw [map_inv] at h ⊢
    rw [map_inv]
    have h' := congrArg (Q.normalizerMonoidHom t).symm h
    simpa using h'.symm

theorem extensionDomainSubgroup_coe {P Q : Subgroup S} (e : P ≃* Q) :
    (F.extensionDomainSubgroup e : Set S) = F.extensionDomain e := rfl

theorem le_extensionDomainSubgroup {P Q : Subgroup S} (e : P ≃* Q) :
    P ≤ F.extensionDomainSubgroup e := by
  intro x hx
  refine ⟨⟨x, Subgroup.le_normalizer hx⟩, rfl,
    ⟨(e ⟨x, hx⟩).val, Subgroup.le_normalizer (e ⟨x, hx⟩).property⟩, ?_⟩
  intro y
  apply Subtype.ext
  change (e (⟨x, hx⟩ * y * (⟨x, hx⟩ : P)⁻¹)).val =
    (e ⟨x, hx⟩).val * (e y).val * (e ⟨x, hx⟩).val⁻¹
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem centralizer_le_extensionDomainSubgroup {P Q : Subgroup S} (e : P ≃* Q) :
    Subgroup.centralizer (P : Set S) ≤ F.extensionDomainSubgroup e := by
  intro x hx
  refine ⟨⟨x, Subgroup.centralizer_le_normalizer (P : Set S) hx⟩, rfl, 1, ?_⟩
  intro y
  have hfix : P.normalizerMonoidHom
      ⟨x, Subgroup.centralizer_le_normalizer (P : Set S) hx⟩ y = y := by
    apply Subtype.ext
    change x * y.val * x⁻¹ = y.val
    rw [← (Subgroup.mem_centralizer_iff.mp hx) y.val y.property,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [hfix]
  simp

/-- Receptivity with the full, exact extension domain. -/
def Receptive (P : Subgroup S) : Prop :=
  ∀ (Q : Subgroup S) (e : Q ≃* P), F.IsHom e.toMonoidHom →
    ∃ f : F.extensionDomainSubgroup e →* (⊤ : Subgroup S), F.IsHom f ∧
      ∀ x : Q, (f ⟨x.val, F.le_extensionDomainSubgroup e x.property⟩).val = (e x).val

theorem receptive_of_saturated_fullyCentralized (p : ℕ) (sat : F.Saturated p)
    {P : Subgroup S} (hP : F.FullyCentralized P) : F.Receptive P := by
  intro Q e he
  obtain ⟨N, hQN, hN, g, hg, hge⟩ := sat.extension e he hP
  have hle : F.extensionDomainSubgroup e ≤ N := by
    intro x hx
    rw [← SetLike.mem_coe, hN]
    exact hx
  exact ⟨g.comp (subgroupInclusion _ _ hle),
    F.comp_mem _ _ (F.inclusion_mem hle) hg, hge⟩

/-- Receptivity implies full centralization, by restricting each extension
to an injection from the source centralizer into the target centralizer. -/
theorem Receptive.fullyCentralized {P : Subgroup S} (hP : F.Receptive P) :
    F.FullyCentralized P := by
  intro Q e he
  obtain ⟨f, hf, hfe⟩ := hP Q e.symm (F.inverse_mem e he)
  let i : Subgroup.centralizer (Q : Set S) →* F.extensionDomainSubgroup e.symm :=
    subgroupInclusion _ _ (F.centralizer_le_extensionDomainSubgroup e.symm)
  have hmem : ∀ x : Subgroup.centralizer (Q : Set S),
      (f (i x)).val ∈ Subgroup.centralizer (P : Set S) := by
    intro x
    apply Subgroup.mem_centralizer_iff.mpr
    intro p hp
    let q : Q := e ⟨p, hp⟩
    let q' : F.extensionDomainSubgroup e.symm :=
      ⟨q.val, F.le_extensionDomainSubgroup e.symm q.property⟩
    have hq : (f q').val = p := by
      exact (hfe q).trans (congrArg Subtype.val (e.symm_apply_apply ⟨p, hp⟩))
    have hc : q' * i x = i x * q' := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp x.property) q.val q.property
    have hm := congrArg (fun y => (f y).val) hc
    simpa only [map_mul, Subgroup.coe_mul, hq] using hm
  let g : Subgroup.centralizer (Q : Set S) → Subgroup.centralizer (P : Set S) :=
    fun x => ⟨(f (i x)).val, hmem x⟩
  apply Nat.card_le_card_of_injective g
  intro x y h
  apply Subtype.ext
  have h' : f (i x) = f (i y) := Subtype.ext
    (congrArg (fun z : Subgroup.centralizer (P : Set S) => z.val) h)
  exact congrArg (fun z : F.extensionDomainSubgroup e.symm => z.val) (F.injective f hf h')

end Sharpness.FusionSystem
