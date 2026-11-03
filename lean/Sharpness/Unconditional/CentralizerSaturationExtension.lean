import Sharpness.Unconditional.CentralizerConstructionAutomorphisms
import Sharpness.Unconditional.CentralizerSaturationReceptive

/-! Lifting exact extension domains to the join with a central subgroup. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S]

theorem centralizingHom_of_fixes (F : FusionSystem S) {Z P Q : Subgroup S}
    (hZP : Z ≤ P) (f : P →* Q) (hf : F.IsHom f)
    (hfix : ∀ z : Z, (f ⟨z.val, hZP z.property⟩).val = z.val) :
    F.CentralizingHom Z f := by
  let pre := subgroupInclusion (P ⊔ Z) P (sup_le le_rfl hZP)
  let post := subgroupInclusion Q (Q ⊔ Z) le_sup_left
  exact ⟨hf, post.comp (f.comp pre),
    F.comp_mem _ _ (F.comp_mem _ _ (F.inclusion_mem _) hf) (F.inclusion_mem _),
    (fun _ => rfl), hfix⟩

theorem normalizer_join_of_central {P Z : Subgroup S}
    (hZ : Z ≤ Subgroup.center S) (n : Subgroup.normalizer (P : Set S)) :
    n.val ∈ Subgroup.normalizer ((P ⊔ Z : Subgroup S) : Set S) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp n.property]
  have hmap : Z.map (MulAut.conj n.val) = Z := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      have hc := (Subgroup.mem_center_iff.mp (hZ hz)) n.val
      change n.val * z * n.val⁻¹ ∈ Z
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hz
    · intro z hz
      refine ⟨z, hz, ?_⟩
      have hc := (Subgroup.mem_center_iff.mp (hZ hz)) n.val
      change n.val * z * n.val⁻¹ = z
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [hmap]

theorem centralizing_extension_intertwines {Z P Q : Subgroup S}
    (hZ : Z ≤ Subgroup.center S) (e : P ≃* Q)
    (g : (P ⊔ Z : Subgroup S) ≃* (Q ⊔ Z : Subgroup S))
    (hgP : ∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (e x).val)
    (hgZ : ∀ z : Z, (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val)
    (n : Subgroup.normalizer (P : Set S)) (t : Subgroup.normalizer (Q : Set S))
    (hconj : ∀ x : P, e (P.normalizerMonoidHom n x) = Q.normalizerMonoidHom t (e x)) :
    ∀ x : (P ⊔ Z : Subgroup S),
      g ((P ⊔ Z).normalizerMonoidHom ⟨n.val, normalizer_join_of_central hZ n⟩ x) =
      (Q ⊔ Z).normalizerMonoidHom ⟨t.val, normalizer_join_of_central hZ t⟩ (g x) := by
  have hh : g.toMonoidHom.comp
        ((P ⊔ Z).normalizerMonoidHom ⟨n.val, normalizer_join_of_central hZ n⟩).toMonoidHom =
      ((Q ⊔ Z).normalizerMonoidHom ⟨t.val, normalizer_join_of_central hZ t⟩).toMonoidHom.comp
        g.toMonoidHom := by
    apply join_hom_ext
    · intro x
      apply Subtype.ext
      change (g ⟨(P.normalizerMonoidHom n x).val,
        Subgroup.mem_sup_left (P.normalizerMonoidHom n x).property⟩).val =
        t.val * (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val * t.val⁻¹
      rw [hgP, hgP]
      exact congrArg Subtype.val (hconj x)
    · intro z
      have hn : n.val * z.val * n.val⁻¹ = z.val := by
        rw [(Subgroup.mem_center_iff.mp (hZ z.property)) n.val,
          mul_assoc, mul_inv_cancel, mul_one]
      have ht : t.val * z.val * t.val⁻¹ = z.val := by
        rw [(Subgroup.mem_center_iff.mp (hZ z.property)) t.val,
          mul_assoc, mul_inv_cancel, mul_one]
      have hn' : (P ⊔ Z).normalizerMonoidHom
          ⟨n.val, normalizer_join_of_central hZ n⟩
          ⟨z.val, Subgroup.mem_sup_right z.property⟩ =
            ⟨z.val, Subgroup.mem_sup_right z.property⟩ := Subtype.ext hn
      change g ((P ⊔ Z).normalizerMonoidHom
          ⟨n.val, normalizer_join_of_central hZ n⟩
          ⟨z.val, Subgroup.mem_sup_right z.property⟩) = _
      rw [hn']
      apply Subtype.ext
      change (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val =
        t.val * (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val * t.val⁻¹
      rw [hgZ, ht]
  exact fun x => congrArg (fun f => f x) hh

variable [Finite S]

theorem centralizing_extensionDomain_ambient_le (F : FusionSystem S) (T : Subgroup S)
    (H : FusionSystem T) {Z P Q : Subgroup T}
    (hZ : Z ≤ Subgroup.center T) (e : P ≃* Q)
    (g : (P ⊔ Z : Subgroup T) ≃* (Q ⊔ Z : Subgroup T))
    (hgP : ∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (e x).val)
    (hgZ : ∀ z : Z, (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val) :
    ambientSubgroup T (H.extensionDomainSubgroup e) ≤
      F.extensionDomainSubgroup ((subgroupAmbientEquiv T (P ⊔ Z)).symm.trans
        (g.trans (subgroupAmbientEquiv T (Q ⊔ Z)))) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨n, hny, t, ht⟩ := hy
  subst y
  let nJ : Subgroup.normalizer ((P ⊔ Z : Subgroup T) : Set T) :=
    ⟨n.val, normalizer_join_of_central hZ n⟩
  let tJ : Subgroup.normalizer ((Q ⊔ Z : Subgroup T) : Set T) :=
    ⟨t.val, normalizer_join_of_central hZ t⟩
  have hnA : n.val.val ∈ Subgroup.normalizer (ambientSubgroup T (P ⊔ Z) : Set S) :=
    Subgroup.le_normalizer_map T.subtype ⟨n.val, nJ.property, rfl⟩
  have htA : t.val.val ∈ Subgroup.normalizer (ambientSubgroup T (Q ⊔ Z) : Set S) :=
    Subgroup.le_normalizer_map T.subtype ⟨t.val, tJ.property, rfl⟩
  refine ⟨⟨n.val.val, hnA⟩, rfl, ⟨t.val.val, htA⟩, ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := (subgroupAmbientEquiv T (P ⊔ Z)).surjective x
  have hnEq : (ambientSubgroup T (P ⊔ Z)).normalizerMonoidHom ⟨n.val.val, hnA⟩
      (subgroupAmbientEquiv T (P ⊔ Z) z) =
        subgroupAmbientEquiv T (P ⊔ Z) ((P ⊔ Z).normalizerMonoidHom nJ z) := by
    apply Subtype.ext
    rfl
  change ambientHom T g.toMonoidHom _ =
    (ambientSubgroup T (Q ⊔ Z)).normalizerMonoidHom ⟨t.val.val, htA⟩
      (ambientHom T g.toMonoidHom (subgroupAmbientEquiv T (P ⊔ Z) z))
  rw [hnEq, ambientHom_apply, ambientHom_apply]
  apply Subtype.ext
  exact congrArg (fun y : (Q ⊔ Z : Subgroup T) => y.val.val)
    (centralizing_extension_intertwines hZ e g hgP hgZ n t ht z)

/-- The receptivity part of centralizer saturation holds whenever the
target join with `E` is fully centralized in the ambient fusion system. -/
theorem centralizerSystem_receptive_of_join_fullyCentralized
    (F : FusionSystem S) (p : ℕ) (sat : F.Saturated p) (E : F.ElementaryCategory p)
    (Q : Subgroup (F.centralizerGroup p E))
    (hQ : F.FullyCentralized (ambientSubgroup (F.centralizerGroup p E)
      (Q ⊔ F.elementaryInCentralizer p E))) :
    (F.centralizerSystem p E).Receptive Q := by
  let T := F.centralizerGroup p E
  let Z := F.elementaryInCentralizer p E
  let C := F.centralizerSystem p E
  have hZ : Z ≤ Subgroup.center T := (F.centralizerSystem_central p E).in_center
  intro P e he
  obtain ⟨g, hg, hgP, hgZ⟩ :=
    (F.subgroupRestriction T).centralizingHom_equiv_extension Z e he
  let a := (subgroupAmbientEquiv T (P ⊔ Z)).symm.trans
    (g.trans (subgroupAmbientEquiv T (Q ⊔ Z)))
  have ha : F.IsHom a.toMonoidHom := hg
  obtain ⟨M, hAM, hM, f, hf, hfa⟩ := sat.extension a ha hQ
  let N := C.extensionDomainSubgroup e
  have hPN : P ≤ N := C.le_extensionDomainSubgroup e
  have hZN : Z ≤ N := (hZ.trans (Subgroup.center_le_centralizer _)).trans
    (C.centralizer_le_extensionDomainSubgroup e)
  have hNM : ambientSubgroup T N ≤ M := by
    intro x hx
    rw [← SetLike.mem_coe, hM]
    exact centralizing_extensionDomain_ambient_le F T C hZ e g hgP hgZ hx
  have hfixZ : ∀ z : Z,
      (f ⟨z.val.val, hNM ⟨z.val, hZN z.property, rfl⟩⟩).val = z.val.val := by
    intro z
    let zJ : (P ⊔ Z : Subgroup T) := ⟨z.val, Subgroup.mem_sup_right z.property⟩
    have hh := hfa (subgroupAmbientEquiv T (P ⊔ Z) zJ)
    change (f ⟨z.val.val, _⟩).val =
      (ambientHom T g.toMonoidHom (subgroupAmbientEquiv T (P ⊔ Z) zJ)).val at hh
    rw [ambientHom_apply] at hh
    exact hh.trans (congrArg (fun t : T => t.val) (hgZ z))
  have hmem : ∀ n : N,
      (f ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩).val ∈ T := by
    intro n
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    let zT : T := ⟨z, F.elementary_le_centralizer p E hz⟩
    let zZ : Z := ⟨zT, hz⟩
    let zn : M := ⟨z, hNM ⟨zT, hZN hz, rfl⟩⟩
    let nn : M := ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩
    have hcomm : zn * nn = nn * zn := by
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp n.val.property) z hz
    have hh := congrArg (fun m : M => (f m).val) hcomm
    have hzz : (f zn).val = z := hfixZ zZ
    simpa only [map_mul, Subgroup.coe_mul, hzz] using hh
  let fN : N →* (⊤ : Subgroup T) :=
    { toFun n := ⟨⟨(f ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩).val, hmem n⟩, trivial⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : (⊤ : Subgroup S) => x.val) f.map_one
      map_mul' n m := by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : (⊤ : Subgroup S) => x.val)
          (f.map_mul ⟨n.val.val, hNM ⟨n.val, n.property, rfl⟩⟩
            ⟨m.val.val, hNM ⟨m.val, m.property, rfl⟩⟩) }
  have hfN : F.IsHom (ambientHom T fN) := by
    apply F.codomain_restrict_mem (f.comp (subgroupInclusion _ _ hNM))
      (F.comp_mem _ _ (F.inclusion_mem hNM) hf) le_top (ambientHom T fN)
    apply MonoidHom.ext
    intro x
    obtain ⟨n, rfl⟩ := (subgroupAmbientEquiv T N).surjective x
    apply Subtype.ext
    change (ambientHom T fN (subgroupAmbientEquiv T N n)).val = _
    rw [ambientHom_apply]
    rfl
  have hfixN : ∀ z : Z, (fN ⟨z.val, hZN z.property⟩).val = z.val := by
    intro z
    apply Subtype.ext
    exact hfixZ z
  refine ⟨fN, centralizingHom_of_fixes (F.subgroupRestriction T) hZN fN hfN hfixN, ?_⟩
  intro x
  apply Subtype.ext
  let xJ : (P ⊔ Z : Subgroup T) := ⟨x.val, Subgroup.mem_sup_left x.property⟩
  have hh := hfa (subgroupAmbientEquiv T (P ⊔ Z) xJ)
  change (f ⟨x.val.val, _⟩).val =
    (ambientHom T g.toMonoidHom (subgroupAmbientEquiv T (P ⊔ Z) xJ)).val at hh
  rw [ambientHom_apply] at hh
  exact hh.trans (congrArg (fun t : T => t.val) (hgP x))

end Sharpness.FusionSystem
