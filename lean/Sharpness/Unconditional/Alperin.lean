import Sharpness.Unconditional.AlperinGeneration
import Sharpness.Unconditional.AlperinCentric

/-! Alperin generation by centric automorphisms, proved by descending
subgroup order from the concrete saturation axioms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
attribute [local irreducible] AlperinStronglyGenerated

def alperinMulEquivOfIso {P Q : F.Object} (e : P ≅ Q) : P.subgroup ≃* Q.subgroup :=
  MulEquiv.ofBijective e.hom.val ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨F.injective _ e.hom.property, le_antisymm (F.order_mono e.hom) (F.order_mono e.inv)⟩)

private theorem subgroup_card_lt {P Q : Subgroup S} (h : P < Q) :
    Nat.card P < Nat.card Q := by
  apply lt_of_not_ge
  intro hc
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hc)

/-- Every fusion isomorphism, together with each of its restrictions, is
generated in the original orbit-category sense. -/
theorem alperinStronglyGenerated_iso (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P Q : Subgroup S}
    (e : P ≃* Q) (he : F.IsHom e.toMonoidHom) :
    F.AlperinStronglyGenerated (F.isoOfMulEquiv e he).hom := by
  have main : ∀ n : ℕ, ∀ (P Q : Subgroup S), Nat.card S - Nat.card P = n →
      ∀ (e : P ≃* Q) (he : F.IsHom e.toMonoidHom),
        F.AlperinStronglyGenerated (F.isoOfMulEquiv e he).hom := by
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
        exact F.alperinStronglyGenerated_centric_aut F.top_centric (F.isoOfMulEquiv e he)
      have hbig : ∀ {A B : F.Object} (f : A ⟶ B),
          Nat.card P < Nat.card A.subgroup → F.AlperinStronglyGenerated f := by
        intro A B f hA
        let i := F.imageIso f
        let d := F.alperinMulEquivOfIso i
        have hd : F.IsHom d.toMonoidHom := i.hom.property
        have hm : Nat.card S - Nat.card A.subgroup < n := by
          have hAS := A.subgroup.card_le_card_group
          omega
        have hi := ih _ hm A.subgroup (F.imageSubgroup f) rfl d hd
        have hi' : F.AlperinStronglyGenerated i.hom := hi
        have hh := F.alperinStronglyGenerated_comp hi'
          (F.alperinStronglyGenerated_inclusion (F.image_le f))
        change F.AlperinStronglyGenerated (F.toImage f ≫ F.inclusion (F.image_le f)) at hh
        rwa [image_factorization] at hh
      have hnormalize : ∀ (A R : Subgroup S), Nat.card A = Nat.card P →
          ∀ (d : A ≃* R), F.IsHom d.toMonoidHom → F.FullyNormalized R →
          ∃ (ψ : A ≃* R) (hψ : F.IsHom ψ.toMonoidHom),
            F.AlperinStronglyGenerated (F.isoOfMulEquiv ψ hψ).hom ∧
            F.AlperinStronglyGenerated (F.isoOfMulEquiv ψ hψ).inv := by
        intro A R hAP d hd hR
        have hAtop : A ≠ ⊤ := by
          intro ht
          apply hPtop
          apply P.eq_top_of_card_eq
          rw [← hAP, ht, Subgroup.card_top]
        have hAN := proper_subgroup_lt_normalizer p hS hAtop
        have hlarge : Nat.card P < Nat.card (Subgroup.normalizer (A : Set S)) := by
          rw [← hAP]
          exact subgroup_card_lt hAN
        obtain ⟨ψ, hψ, f, hf, hext⟩ :=
          F.exists_normalizer_extension_to_fullyNormalized p hS sat d hd hR
        let N := Subgroup.normalizer (A : Set S)
        let f' : (⟨N⟩ : F.Object) ⟶ ⟨⊤⟩ := ⟨f, hf⟩
        let i := F.imageIso f'
        have hRimage : R ≤ F.imageSubgroup f' := by
          intro r hr
          refine ⟨⟨(ψ.symm ⟨r, hr⟩).val,
            Subgroup.le_normalizer (ψ.symm ⟨r, hr⟩).property⟩, ?_⟩
          change (f _).val = r
          rw [hext]
          exact congrArg Subtype.val (ψ.apply_symm_apply ⟨r, hr⟩)
        have hi : Nat.card P < Nat.card (F.imageSubgroup f') := by
          have hc := Nat.card_congr (F.alperinMulEquivOfIso i).toEquiv
          exact hc ▸ hlarge
        refine ⟨ψ, hψ, ?_, ?_⟩
        · exact F.alperinStronglyGenerated_restrict (hbig f' hlarge)
            Subgroup.le_normalizer le_top (F.isoOfMulEquiv ψ hψ).hom (fun x => (hext x).symm)
        · apply F.alperinStronglyGenerated_restrict (hbig i.inv hi)
            hRimage Subgroup.le_normalizer (F.isoOfMulEquiv ψ hψ).inv
          intro r
          let a : N := ⟨(ψ.symm r).val, Subgroup.le_normalizer (ψ.symm r).property⟩
          have heq : i.hom.val a = ⟨r.val, hRimage r.property⟩ := by
            apply Subtype.ext
            change (f a).val = r.val
            rw [hext]
            exact congrArg Subtype.val (ψ.apply_symm_apply r)
          have hcancel := congrArg (fun m : (⟨N⟩ : F.Object) ⟶ ⟨N⟩ =>
            (m.val a).val) i.hom_inv_id
          change (ψ.symm r).val = (i.inv.val _).val
          rw [← heq]
          exact hcancel.symm
      obtain ⟨R, d, hd, hR⟩ := F.exists_fullyNormalized P
      obtain ⟨ψ, hψ, hψgen, _⟩ := hnormalize P R rfl d hd hR
      obtain ⟨χ, hχ, _, hχgen⟩ := hnormalize Q R hPQ.symm (e.symm.trans d)
        (F.comp_mem _ _ (F.inverse_mem e he) hd) hR
      let a : MulAut R := ψ.symm.trans (e.trans χ)
      have ha : F.IsHom a.toMonoidHom := F.comp_mem _ _
        (F.comp_mem _ _ (F.inverse_mem ψ hψ) he) hχ
      have hagen : F.AlperinStronglyGenerated (F.isoOfMulEquiv a ha).hom := by
        by_cases hRc : F.IsCentric R
        · exact F.alperinStronglyGenerated_centric_aut hRc (F.isoOfMulEquiv a ha)
        · obtain ⟨N, hRN, f, hf, hext⟩ := F.noncentric_automorphism_extension
            p sat (sat.fully_normalized R hR).1 hRc a ha
          have hPR : Nat.card P = Nat.card R := Nat.card_congr d.toEquiv
          have hlarge : Nat.card P < Nat.card N := by
            rw [hPR]
            exact subgroup_card_lt hRN
          exact F.alperinStronglyGenerated_restrict
            (hbig (show (⟨N⟩ : F.Object) ⟶ ⟨⊤⟩ from ⟨f, hf⟩) hlarge)
            hRN.le le_top (F.isoOfMulEquiv a ha).hom (fun x => (hext x).symm)
      have hcomp := F.alperinStronglyGenerated_comp
        (F.alperinStronglyGenerated_comp hψgen hagen) hχgen
      have heq : ((F.isoOfMulEquiv ψ hψ).hom ≫ (F.isoOfMulEquiv a ha).hom) ≫
          (F.isoOfMulEquiv χ hχ).inv = (F.isoOfMulEquiv e he).hom := by
        apply Subtype.ext
        ext x
        change (χ.symm (a (ψ x))).val = (e x).val
        simp [a]
      exact heq ▸ hcomp
  exact main _ P Q rfl e he

/-- The Alperin input required by the manuscript, constructed from saturation. -/
def alperinInput (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S)
    (sat : F.Saturated p) : F.AlperinInput where
  theorem_A_10 := by
    intro P Q f
    rcases P with ⟨P⟩
    rcases Q with ⟨Q⟩
    obtain ⟨g, rfl⟩ := F.toOrbit.map_surjective f
    let i := F.imageIso g
    let e := F.alperinMulEquivOfIso i
    have he : F.IsHom e.toMonoidHom := i.hom.property
    have hi : F.AlperinStronglyGenerated i.hom :=
      F.alperinStronglyGenerated_iso p hS sat e he
    have hh := F.alperinStronglyGenerated_comp hi
      (F.alperinStronglyGenerated_inclusion (F.image_le g))
    apply F.alperinStronglyGenerated_generated
    change F.AlperinStronglyGenerated (F.toImage g ≫ F.inclusion (F.image_le g)) at hh
    rwa [image_factorization] at hh

end Sharpness.FusionSystem
