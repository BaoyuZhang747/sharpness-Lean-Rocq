import Sharpness.Unconditional.AlperinNormalizer
import Sharpness.Unconditional.CentralizerSaturationReceptive
import Sharpness.Unconditional.SaturationNormalizerMap

/-! The saturation criterion using Sylow automorphisms and receptivity at
fully normalized subgroups. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem extension_conjugation {P Q N : Subgroup S} (e : P ≃* Q)
    (hPN : P ≤ N) (hNP : N ≤ Subgroup.normalizer (P : Set S))
    (f : N →* (⊤ : Subgroup S))
    (hext : ∀ x : P, (f ⟨x.val, hPN x.property⟩).val = (e x).val)
    (n : N) (x : P) :
    (f n).val * (e x).val * (f n).val⁻¹ =
      (e (P.normalizerMonoidHom ⟨n.val, hNP n.property⟩ x)).val := by
  let nx : P := P.normalizerMonoidHom ⟨n.val, hNP n.property⟩ x
  have heq : n * ⟨x.val, hPN x.property⟩ * n⁻¹ =
      (⟨nx.val, hPN nx.property⟩ : N) := by
    apply Subtype.ext
    rfl
  have h := congrArg (fun z : N => (f z).val) heq
  simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hext] using h

/-- At a fully centralized source, an injective extension of a fusion
isomorphism on the whole normalizer contains the target centralizer in its image. -/
theorem centralizer_le_normalizerExtension_image {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) (hP : F.FullyCentralized P)
    (f : Subgroup.normalizer (P : Set S) →* (⊤ : Subgroup S))
    (hf : F.IsHom f)
    (hext : ∀ x : P,
      (f ⟨x.val, Subgroup.le_normalizer x.property⟩).val = (e x).val) :
    Subgroup.centralizer (Q : Set S) ≤
      F.imageSubgroup (show (⟨Subgroup.normalizer (P : Set S)⟩ : F.Object) ⟶ ⟨⊤⟩ from ⟨f, hf⟩) := by
  let i : Subgroup.centralizer (P : Set S) →* Subgroup.normalizer (P : Set S) :=
    subgroupInclusion _ _ (Subgroup.centralizer_le_normalizer (P : Set S))
  have hmem : ∀ x : Subgroup.centralizer (P : Set S),
      (f (i x)).val ∈ Subgroup.centralizer (Q : Set S) := by
    intro x
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    let a := e.symm ⟨y, hy⟩
    have hfy : (f ⟨a.val, Subgroup.le_normalizer a.property⟩).val = y := by
      rw [hext]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    have hcomm : (⟨a.val, Subgroup.le_normalizer a.property⟩ :
        Subgroup.normalizer (P : Set S)) * i x = i x * ⟨a.val, Subgroup.le_normalizer a.property⟩ := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp x.property) a.val a.property
    have h := congrArg (fun z => (f z).val) hcomm
    simpa only [map_mul, Subgroup.coe_mul, hfy] using h
  let c : Subgroup.centralizer (P : Set S) → Subgroup.centralizer (Q : Set S) :=
    fun x => ⟨(f (i x)).val, hmem x⟩
  have hinj : Function.Injective c := by
    intro x y h
    apply Subtype.ext
    have h' : f (i x) = f (i y) := Subtype.ext
      (congrArg (fun z : Subgroup.centralizer (Q : Set S) => z.val) h)
    exact congrArg (fun z : Subgroup.normalizer (P : Set S) => z.val) (F.injective f hf h')
  have hc : Nat.card (Subgroup.centralizer (P : Set S)) =
      Nat.card (Subgroup.centralizer (Q : Set S)) :=
    le_antisymm (Nat.card_le_card_of_injective c hinj) (hP Q e he)
  have hsurj := ((Nat.bijective_iff_injective_and_card c).mpr ⟨hinj, hc⟩).surjective
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨i x, congrArg Subtype.val hx⟩

/-- Receptivity transports back across an extension on the whole source
normalizer when the source is fully centralized. -/
theorem receptive_of_normalizer_extension {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) (hP : F.FullyCentralized P)
    (hQ : F.Receptive Q)
    (f : Subgroup.normalizer (P : Set S) →* (⊤ : Subgroup S))
    (hf : F.IsHom f)
    (hext : ∀ x : P,
      (f ⟨x.val, Subgroup.le_normalizer x.property⟩).val = (e x).val) :
    F.Receptive P := by
  let f' : (⟨Subgroup.normalizer (P : Set S)⟩ : F.Object) ⟶ ⟨⊤⟩ := ⟨f, hf⟩
  let T := F.imageSubgroup f'
  have hCT : Subgroup.centralizer (Q : Set S) ≤ T :=
    F.centralizer_le_normalizerExtension_image e he hP f hf hext
  intro A d hd
  let d' := d.trans e
  have hd' : F.IsHom d'.toMonoidHom := F.comp_mem _ _ hd he
  have hdom : F.extensionDomainSubgroup d ≤ F.extensionDomainSubgroup d' := by
    rintro x ⟨n, rfl, t, ht⟩
    refine ⟨n, rfl,
      ⟨(f t).val, normalizer_extension_mem_normalizer e f hext t⟩, ?_⟩
    intro a
    change e (d (A.normalizerMonoidHom n a)) = _
    rw [ht a]
    exact normalizer_extension_intertwines e f hext t (d a)
  obtain ⟨g, hg, hgext⟩ := hQ A d' hd'
  let g' := g.comp (subgroupInclusion _ _ hdom)
  have hg' : F.IsHom g' := F.comp_mem _ _ (F.inclusion_mem hdom) hg
  have hnormal : F.extensionDomainSubgroup d' ≤ Subgroup.normalizer (A : Set S) := by
    rintro x ⟨n, rfl, _, _⟩
    exact n.property
  have hmem : ∀ x : F.extensionDomainSubgroup d, (g' x).val ∈ T := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl, t, ht⟩ := hx
    let z : F.extensionDomainSubgroup d := ⟨n.val, ⟨n, rfl, t, ht⟩⟩
    let v : S := (g' z).val
    let w : S := (f t).val
    have hconj (a : A) : v * (d' a).val * v⁻¹ = w * (d' a).val * w⁻¹ := by
      calc
        v * (d' a).val * v⁻¹ =
            (d' (A.normalizerMonoidHom n a)).val :=
          extension_conjugation d' (F.le_extensionDomainSubgroup d') hnormal g hgext
            ⟨n.val, hdom z.property⟩ a
        _ = (e (P.normalizerMonoidHom t (d a))).val :=
          congrArg (fun a : P => (e a).val) (ht a)
        _ = w * (d' a).val * w⁻¹ := normalizer_extension_conjugation e f hext t (d a)
    have hcor : w⁻¹ * v ∈ Subgroup.centralizer (Q : Set S) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro q hq
      have heq : v * q * v⁻¹ = w * q * w⁻¹ := by
        have hh := hconj (d'.symm ⟨q, hq⟩)
        simpa only [MulEquiv.apply_symm_apply] using hh
      calc
        q * (w⁻¹ * v) = w⁻¹ * (w * q * w⁻¹) * v := by group
        _ = w⁻¹ * (v * q * v⁻¹) * v := by rw [← heq]
        _ = (w⁻¹ * v) * q := by group
    have hw : w ∈ T := ⟨t, rfl⟩
    have hv := T.mul_mem hw (hCT hcor)
    simpa only [mul_inv_cancel_left] using hv
  let k : F.extensionDomainSubgroup d →* T :=
    { toFun x := ⟨(g' x).val, hmem x⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) g'.map_one
      map_mul' x y := by
        apply Subtype.ext
        exact congrArg (fun z : (⊤ : Subgroup S) => z.val) (g'.map_mul x y) }
  have hk : F.IsHom k := F.codomain_restrict_mem g' hg' le_top k (by ext x; rfl)
  let i := F.imageIso f'
  let l := (subgroupInclusion (Subgroup.normalizer (P : Set S)) ⊤ le_top).comp
    (i.inv.val.comp k)
  have hl : F.IsHom l := F.comp_mem _ _ (F.comp_mem _ _ hk i.inv.property)
    (F.inclusion_mem le_top)
  refine ⟨l, hl, ?_⟩
  intro a
  let da : Subgroup.normalizer (P : Set S) := ⟨(d a).val, Subgroup.le_normalizer (d a).property⟩
  have heq : i.hom.val da = k ⟨a.val, F.le_extensionDomainSubgroup d a.property⟩ := by
    apply Subtype.ext
    change (f da).val = (g _).val
    rw [hext (d a)]
    exact (hgext a).symm
  have hcancel := congrArg
    (fun m : (⟨Subgroup.normalizer (P : Set S)⟩ : F.Object) ⟶
      ⟨Subgroup.normalizer (P : Set S)⟩ => (m.val da).val) i.hom_inv_id
  change (i.inv.val (k _)).val = (d a).val
  rw [← heq]
  exact hcancel

/-- The BLO saturation axioms follow from the Sylow condition and
receptivity at every fully normalized subgroup. -/
theorem saturated_of_fullyNormalized_sylow_receptive (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S)
    (sylow : ∀ P, F.FullyNormalized P →
      ¬ p ∣ (F.innerSylowSubgroup P).relIndex (F.automorphismSubgroup P))
    (receptive : ∀ P, F.FullyNormalized P → F.Receptive P) : F.Saturated p where
  fully_normalized P hP :=
    ⟨Receptive.fullyCentralized F (receptive P hP), sylow P hP⟩
  extension {P Q} e he hQ := by
    obtain ⟨R, d, hd, hR⟩ := F.exists_fullyNormalized Q
    obtain ⟨ψ, hψ, hdom⟩ :=
      F.exists_iso_extensionDomain_eq_normalizer_of_sylow p hS d hd (sylow R hR)
    obtain ⟨f, hf, hext⟩ := receptive R hR Q ψ hψ
    have hN : Subgroup.normalizer (Q : Set S) ≤ F.extensionDomainSubgroup ψ := by
      intro x hx
      change x ∈ F.extensionDomain ψ
      rw [hdom]
      exact hx
    let f' := f.comp (subgroupInclusion _ _ hN)
    have hf' : F.IsHom f' := F.comp_mem _ _ (F.inclusion_mem hN) hf
    have hext' : ∀ x : Q,
        (f' ⟨x.val, Subgroup.le_normalizer x.property⟩).val = (ψ x).val := hext
    have hQrec : F.Receptive Q := F.receptive_of_normalizer_extension
      ψ hψ hQ (receptive R hR) f' hf' hext'
    obtain ⟨g, hg, hgext⟩ := hQrec P e he
    exact ⟨F.extensionDomainSubgroup e, F.le_extensionDomainSubgroup e, rfl, g, hg, hgext⟩

end Sharpness.FusionSystem
