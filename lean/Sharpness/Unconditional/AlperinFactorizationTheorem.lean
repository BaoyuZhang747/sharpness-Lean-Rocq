import Sharpness.Unconditional.AlperinFactorization

/-! The finite-word form of centric Alperin factorization, with literal equality
of group homomorphisms, proved directly from the saturation axioms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
attribute [local irreducible] StronglyCentricFactorizable

private theorem factorization_subgroup_card_lt {P Q : Subgroup S} (h : P < Q) :
    Nat.card P < Nat.card Q := by
  apply lt_of_not_ge
  intro hc
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hc)

/-- Every fusion isomorphism and all its isomorphic restrictions admit literal finite
words of restrictions of actual centric automorphisms. -/
theorem stronglyCentricFactorizable_iso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) : F.StronglyCentricFactorizable e := by
  have main : ∀ n : ℕ, ∀ (P Q : Subgroup S), Nat.card S - Nat.card P = n →
      ∀ (e : P ≃* Q), F.IsHom e.toMonoidHom → F.StronglyCentricFactorizable e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P Q hmeasure e he
      have hPQ : Nat.card P = Nat.card Q := Nat.card_congr e.toEquiv
      by_cases hPtop : P = ⊤
      · have hQtop : Q = ⊤ := Q.eq_top_of_card_eq (by
          rw [← hPQ, hPtop, Subgroup.card_top])
        subst P
        subst Q
        exact F.stronglyCentricFactorizable_centric_aut F.top_centric e he
      have hbig : ∀ {A B : Subgroup S} (d : A ≃* B), F.IsHom d.toMonoidHom →
          Nat.card P < Nat.card A → F.StronglyCentricFactorizable d := by
        intro A B d hd hA
        have hm : Nat.card S - Nat.card A < n := by
          have hAS := A.card_le_card_group
          omega
        exact ih _ hm A B rfl d hd
      have hnormalize : ∀ (A R : Subgroup S), Nat.card A = Nat.card P →
          ∀ (d : A ≃* R), F.IsHom d.toMonoidHom → F.FullyNormalized R →
          ∃ (ψ : A ≃* R) (hψ : F.IsHom ψ.toMonoidHom),
            F.StronglyCentricFactorizable ψ ∧ F.StronglyCentricFactorizable ψ.symm := by
        intro A R hAP d hd hR
        have hAtop : A ≠ ⊤ := by
          intro ht
          apply hPtop
          apply P.eq_top_of_card_eq
          rw [← hAP, ht, Subgroup.card_top]
        have hAN := proper_subgroup_lt_normalizer p hS hAtop
        have hlarge : Nat.card P < Nat.card (Subgroup.normalizer (A : Set S)) := by
          rw [← hAP]
          exact factorization_subgroup_card_lt hAN
        obtain ⟨ψ, hψ, f, hf, hext⟩ :=
          F.exists_normalizer_extension_to_fullyNormalized p hS sat d hd hR
        let N := Subgroup.normalizer (A : Set S)
        let f' : (⟨N⟩ : F.Object) ⟶ ⟨⊤⟩ := ⟨f, hf⟩
        let i := F.imageIso f'
        let d' := F.alperinMulEquivOfIso i
        have hd' : F.IsHom d'.toMonoidHom := i.hom.property
        have hRimage : R ≤ F.imageSubgroup f' := by
          intro r hr
          refine ⟨⟨(ψ.symm ⟨r, hr⟩).val,
            Subgroup.le_normalizer (ψ.symm ⟨r, hr⟩).property⟩, ?_⟩
          change (f _).val = r
          rw [hext]
          exact congrArg Subtype.val (ψ.apply_symm_apply ⟨r, hr⟩)
        have hi : Nat.card P < Nat.card (F.imageSubgroup f') := by
          have hc := Nat.card_congr d'.toEquiv
          exact hc ▸ hlarge
        refine ⟨ψ, hψ, ?_, ?_⟩
        · exact F.stronglyCentricFactorizable_restrict (hbig d' hd' hlarge)
            Subgroup.le_normalizer hRimage ψ (fun x => (hext x).symm)
        · apply F.stronglyCentricFactorizable_restrict
            (hbig d'.symm (F.inverse_mem d' hd') hi)
            hRimage Subgroup.le_normalizer ψ.symm
          intro r
          let a : N := ⟨(ψ.symm r).val, Subgroup.le_normalizer (ψ.symm r).property⟩
          have heq : d' a = ⟨r.val, hRimage r.property⟩ := by
            apply Subtype.ext
            change (f a).val = r.val
            rw [hext]
            exact congrArg Subtype.val (ψ.apply_symm_apply r)
          change a.val = (d'.symm _).val
          rw [← heq, d'.symm_apply_apply]
      obtain ⟨R, d, hd, hR⟩ := F.exists_fullyNormalized P
      obtain ⟨ψ, hψ, hψgen, _⟩ := hnormalize P R rfl d hd hR
      obtain ⟨χ, hχ, _, hχgen⟩ := hnormalize Q R hPQ.symm (e.symm.trans d)
        (F.comp_mem _ _ (F.inverse_mem e he) hd) hR
      let a : MulAut R := ψ.symm.trans (e.trans χ)
      have ha : F.IsHom a.toMonoidHom := F.comp_mem _ _
        (F.comp_mem _ _ (F.inverse_mem ψ hψ) he) hχ
      have hagen : F.StronglyCentricFactorizable a := by
        by_cases hRc : F.IsCentric R
        · exact F.stronglyCentricFactorizable_centric_aut hRc a ha
        · obtain ⟨N, hRN, f, hf, hext⟩ := F.noncentric_automorphism_extension
            p sat (sat.fully_normalized R hR).1 hRc a ha
          have hPR : Nat.card P = Nat.card R := Nat.card_congr d.toEquiv
          have hlarge : Nat.card P < Nat.card N := by
            rw [hPR]
            exact factorization_subgroup_card_lt hRN
          let f' : (⟨N⟩ : F.Object) ⟶ ⟨⊤⟩ := ⟨f, hf⟩
          let i := F.imageIso f'
          let d' := F.alperinMulEquivOfIso i
          have hd' : F.IsHom d'.toMonoidHom := i.hom.property
          have hRimage : R ≤ F.imageSubgroup f' := by
            intro r hr
            refine ⟨⟨(a.symm ⟨r, hr⟩).val, hRN.le (a.symm ⟨r, hr⟩).property⟩, ?_⟩
            change (f _).val = r
            rw [hext]
            exact congrArg Subtype.val (a.apply_symm_apply ⟨r, hr⟩)
          exact F.stronglyCentricFactorizable_restrict (hbig d' hd' hlarge)
            hRN.le hRimage a (fun x => (hext x).symm)
      have hcomp := F.stronglyCentricFactorizable_trans
        (F.comp_mem _ _ hψ ha)
        (F.stronglyCentricFactorizable_trans hψ hψgen hagen) hχgen
      have heq : (ψ.trans a).trans χ.symm = e := by
        ext x
        simp [a]
      exact heq ▸ hcomp
  exact main _ P Q rfl e he

/-- Centric Alperin factorization for every fusion isomorphism, with a literal finite
list and exact equality of the original homomorphisms. -/
theorem exists_centricFactorization_iso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) :
    ∃ l : List F.CentricAutomorphism, ∃ w : F.CentricFactorization P Q l,
      w.comp.toMonoidHom = e.toMonoidHom := by
  have h := F.stronglyCentricFactorizable_iso p hS sat e he
  unfold StronglyCentricFactorizable at h
  obtain ⟨l, w, hw⟩ := h le_rfl le_rfl e (fun _ => rfl)
  exact ⟨l, w, congrArg MulEquiv.toMonoidHom hw⟩

/-- An arbitrary allowed homomorphism is a finite word onto its actual image followed
by the inclusion of that image into the stated codomain. -/
theorem exists_centricFactorization_hom (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (f : P →* Q) (hf : F.IsHom f) :
    ∃ l : List F.CentricAutomorphism,
      ∃ w : F.CentricFactorization P (F.imageSubgroup (show
          (⟨P⟩ : F.Object) ⟶ ⟨Q⟩ from ⟨f, hf⟩)) l,
        (subgroupInclusion _ Q (F.image_le ⟨f, hf⟩)).comp w.comp.toMonoidHom = f := by
  let f' : (⟨P⟩ : F.Object) ⟶ ⟨Q⟩ := ⟨f, hf⟩
  let i := F.imageIso f'
  let e := F.alperinMulEquivOfIso i
  have he : F.IsHom e.toMonoidHom := i.hom.property
  obtain ⟨l, w, hw⟩ := F.exists_centricFactorization_iso p hS sat e he
  refine ⟨l, w, ?_⟩
  rw [hw]
  rfl

end Sharpness.FusionSystem
