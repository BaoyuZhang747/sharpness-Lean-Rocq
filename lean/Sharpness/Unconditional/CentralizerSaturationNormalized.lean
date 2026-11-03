import Sharpness.Unconditional.CentralizerSaturationKBridge
import Sharpness.Unconditional.CentralizerSaturationNormalizer

/-! Centralizer normalizers dominate all transported joint K-normalizers. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

private theorem normalizes_of_intertwines {G : Type u} [Group G]
    {P Q : Subgroup G} (v : P ≃* Q) (a : MulAut P) (n : G)
    (h : ∀ x : P, n * (v x).val * n⁻¹ = (v (a x)).val) :
    n ∈ Subgroup.normalizer (Q : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm
  · rintro y ⟨q, hq, rfl⟩
    obtain ⟨x, hx⟩ := v.surjective ⟨q, hq⟩
    have hxv := congrArg Subtype.val hx
    change (v x).val = q at hxv
    change n * q * n⁻¹ ∈ Q
    rw [← hxv, h]
    exact (v (a x)).property
  · intro q hq
    let x := a.symm (v.symm ⟨q, hq⟩)
    refine ⟨(v x).val, (v x).property, ?_⟩
    change n * (v x).val * n⁻¹ = q
    rw [h]
    exact congrArg (fun z : Q => z.val)
      ((congrArg v (a.apply_symm_apply (v.symm ⟨q, hq⟩))).trans
        (v.apply_symm_apply ⟨q, hq⟩))

theorem centralizer_transported_kNormalizer_card_le (p : ℕ) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (P : Subgroup (F.centralizerGroup p E))
    (hP : (F.centralizerSystem p E).FullyNormalized P)
    (R : Subgroup S)
    (e : ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E) ≃* R)
    (he : F.IsHom e.toMonoidHom) :
    Nat.card (F.kNormalizer R (F.kTransport e he (F.centralizerJoinK p E P))) ≤
      Nat.card (Subgroup.normalizer (P : Set (F.centralizerGroup p E))) := by
  let T := F.centralizerGroup p E
  let Z := F.elementaryInCentralizer p E
  let C := F.centralizerSystem p E
  let A := ambientSubgroup T (P ⊔ Z)
  let K := F.centralizerJoinK p E P
  let L := F.kNormalizer R (F.kTransport e he K)
  have hEA : E.obj.subgroup ≤ A := by
    intro z hz
    exact ⟨⟨z, F.elementary_le_centralizer p E hz⟩, Subgroup.mem_sup_right hz, rfl⟩
  let eEhom : E.obj.subgroup →* R := e.toMonoidHom.comp (subgroupInclusion _ _ hEA)
  have heEhom : F.IsHom eEhom := F.comp_mem _ _ (F.inclusion_mem hEA) he
  let eEraw : E.obj.subgroup →* S := R.subtype.comp eEhom
  let D : Subgroup S := eEraw.range
  have heEraw_inj : Function.Injective eEraw :=
    Subtype.val_injective.comp (F.injective eEhom heEhom)
  let eE : E.obj.subgroup ≃* D := MonoidHom.ofInjective heEraw_inj
  have hDR : D ≤ R := by
    rintro z ⟨x, rfl⟩
    exact (eEhom x).property
  have heE : F.IsHom eE.toMonoidHom := by
    apply F.codomain_restrict_mem eEhom heEhom hDR eE.toMonoidHom
    ext z
    rfl
  obtain ⟨b, hb, hbe⟩ := F.centralizer_extension_of_fullyCentralized p sat
    eE.symm (F.inverse_mem eE heE) E.property.2.2.2
  have hRC : R ≤ Subgroup.centralizer (D : Set S) := by
    intro r hr
    apply Subgroup.mem_centralizer_iff.mpr
    rintro d ⟨z, rfl⟩
    have hc : (⟨z.val, hEA z.property⟩ : A) * e.symm ⟨r, hr⟩ =
        e.symm ⟨r, hr⟩ * ⟨z.val, hEA z.property⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        (ambientSubgroup_le T (P ⊔ Z) (e.symm ⟨r, hr⟩).property)) z.val z.property
    have hm := congrArg (fun a : A => (e a).val) hc
    change (e (⟨z.val, hEA z.property⟩ : A)).val * r =
      r * (e (⟨z.val, hEA z.property⟩ : A)).val
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using hm
  let f : A →* T := b.comp ((subgroupInclusion R _ hRC).comp e.toMonoidHom)
  have hf : F.IsHom f := F.comp_mem _ _ (F.comp_mem _ _ he (F.inclusion_mem hRC)) hb
  have hfix : ∀ z : Z, f (subgroupAmbientEquiv T (P ⊔ Z)
      ⟨z.val, Subgroup.mem_sup_right z.property⟩) = z.val := by
    intro z
    apply Subtype.ext
    let zE : E.obj.subgroup := ⟨z.val.val, z.property⟩
    have hh := hbe (eE zE) (hRC (eEhom zE).property)
    rw [MulEquiv.symm_apply_apply] at hh
    exact hh
  obtain ⟨U, v, hv, hvq⟩ := F.centralizerSystem_conjugate_of_join_map p E P f hf hfix
  have hLC : L ≤ Subgroup.centralizer (D : Set S) := by
    intro n hn
    obtain ⟨hnR, hnK⟩ := (F.mem_kNormalizer_iff R (F.kTransport e he K) n).mp hn
    obtain ⟨a, ha, hat⟩ := hnK
    apply Subgroup.mem_centralizer_iff.mpr
    rintro d ⟨z, rfl⟩
    let zT : T := ⟨z.val, F.elementary_le_centralizer p E z.property⟩
    let zZ : Z := ⟨zT, z.property⟩
    have haz : a.val (⟨z.val, hEA z.property⟩ : A) = ⟨z.val, hEA z.property⟩ :=
      Subtype.ext (F.centralizerJoinK_fixes p E P ⟨a, ha⟩ zZ)
    have hh := congrArg (fun a : F.automorphismSubgroup R =>
      (a.val (e ⟨z.val, hEA z.property⟩)).val) hat
    change (e (a.val (e.symm (e ⟨z.val, hEA z.property⟩)))).val =
      n * (e ⟨z.val, hEA z.property⟩).val * n⁻¹ at hh
    rw [MulEquiv.symm_apply_apply, haz] at hh
    change (e ⟨z.val, hEA z.property⟩).val * n = n * (e ⟨z.val, hEA z.property⟩).val
    calc
      (e ⟨z.val, hEA z.property⟩).val * n =
          (n * (e ⟨z.val, hEA z.property⟩).val * n⁻¹) * n := by rw [← hh]
      _ = n * (e ⟨z.val, hEA z.property⟩).val := by group
  have hnorm : ∀ n : L, b ⟨n.val, hLC n.property⟩ ∈ Subgroup.normalizer (U : Set T) := by
    intro n
    obtain ⟨hnR, hnK⟩ := (F.mem_kNormalizer_iff R (F.kTransport e he K) n.val).mp n.property
    obtain ⟨a, ha, hat⟩ := hnK
    obtain ⟨aJ, haJ⟩ := ha
    let aP := (F.subgroupRestriction T).centralizingJoinRestriction Z P aJ
    apply normalizes_of_intertwines v aP
    intro q
    let qA := subgroupAmbientEquiv T (P ⊔ Z) ⟨q.val, Subgroup.mem_sup_left q.property⟩
    let q'A := subgroupAmbientEquiv T (P ⊔ Z)
      ⟨(aP q).val, Subgroup.mem_sup_left (aP q).property⟩
    have haq : a.val qA = q'A := by
      rw [← haJ]
      change (subgroupAmbientEquiv T (P ⊔ Z))
        (aJ.val ((subgroupAmbientEquiv T (P ⊔ Z)).symm qA)) = q'A
      dsimp only [qA]
      rw [MulEquiv.symm_apply_apply]
      rfl
    have hh := congrArg (fun a : F.automorphismSubgroup R => a.val (e qA)) hat
    change e (a.val (e.symm (e qA))) = R.normalizerMonoidHom ⟨n.val, hnR⟩ (e qA) at hh
    rw [MulEquiv.symm_apply_apply, haq] at hh
    have hhCD : (⟨n.val, hLC n.property⟩ : Subgroup.centralizer (D : Set S)) *
        ⟨(e qA).val, hRC (e qA).property⟩ * ⟨n.val, hLC n.property⟩⁻¹ =
          ⟨(e q'A).val, hRC (e q'A).property⟩ := by
      apply Subtype.ext
      exact congrArg (fun z : R => z.val) hh.symm
    rw [hvq q, hvq (aP q)]
    change b ⟨n.val, hLC n.property⟩ * b ⟨(e qA).val, hRC (e qA).property⟩ *
      (b ⟨n.val, hLC n.property⟩)⁻¹ = b ⟨(e q'A).val, hRC (e q'A).property⟩
    simpa only [map_mul, map_inv] using congrArg b hhCD
  let k : L → Subgroup.normalizer (U : Set T) :=
    fun n => ⟨b ⟨n.val, hLC n.property⟩, hnorm n⟩
  have hk : Function.Injective k := by
    intro n m h
    apply Subtype.ext
    have hh := congrArg (fun x : Subgroup.normalizer (U : Set T) => x.val) h
    exact congrArg (fun x : Subgroup.centralizer (D : Set S) => x.val) (F.injective b hb hh)
  exact (Nat.card_le_card_of_injective k hk).trans (hP U v hv)

/-- A fully normalized centralizer subgroup has a fully K-normalized
ambient join, for the actual joint automorphism subgroup. -/
theorem centralizerSystem_fullyKNormalized (p : ℕ) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (P : Subgroup (F.centralizerGroup p E))
    (hP : (F.centralizerSystem p E).FullyNormalized P) :
    F.FullyKNormalized
      (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E))
      (F.centralizerJoinK p E P) := by
  intro R e he
  refine (F.centralizer_transported_kNormalizer_card_le p sat E P hP R e he).trans_eq ?_
  rw [F.centralizer_kNormalizer_eq p E P]
  exact Nat.card_congr (subgroupAmbientEquiv (F.centralizerGroup p E)
    (Subgroup.normalizer (P : Set (F.centralizerGroup p E)))).toEquiv

end Sharpness.FusionSystem
