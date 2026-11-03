import Sharpness.Unconditional.AlperinNormalizer

/-! Restrictions and products of centric generators in the concrete fusion
orbit category. The stronger predicate below is a proof device for induction;
its conclusion is the existing `AlperinGenerated` predicate. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def AlperinStronglyGenerated {P Q : F.Object} (f : P ⟶ Q) : Prop :=
  ∀ {A B : F.Object} (hAP : A.subgroup ≤ P.subgroup) (hBQ : B.subgroup ≤ Q.subgroup)
    (g : A ⟶ B),
    (∀ x : A.subgroup, (g.val x).val = (f.val ⟨x.val, hAP x.property⟩).val) →
    AlperinGenerated F.centricProperty F.topOrbit F.toTop (F.toOrbit.map g)

theorem alperinStronglyGenerated_generated {P Q : F.Object} {f : P ⟶ Q}
    (hf : F.AlperinStronglyGenerated f) :
    AlperinGenerated F.centricProperty F.topOrbit F.toTop (F.toOrbit.map f) :=
  hf le_rfl le_rfl f (fun _ => rfl)

theorem alperinStronglyGenerated_restrict {P Q A B : F.Object} {f : P ⟶ Q}
    (hf : F.AlperinStronglyGenerated f) (hAP : A.subgroup ≤ P.subgroup)
    (hBQ : B.subgroup ≤ Q.subgroup) (g : A ⟶ B)
    (hg : ∀ x : A.subgroup, (g.val x).val = (f.val ⟨x.val, hAP x.property⟩).val) :
    F.AlperinStronglyGenerated g := by
  intro C D hCA hDB k hk
  apply hf (hCA.trans hAP) (hDB.trans hBQ) k
  intro x
  exact (hk x).trans (hg ⟨x.val, hCA x.property⟩)

theorem alperinStronglyGenerated_inclusion {P Q : F.Object}
    (hPQ : P.subgroup ≤ Q.subgroup) :
    F.AlperinStronglyGenerated (F.inclusion hPQ) := by
  intro A B hAP hBQ g hg
  apply AlperinGenerated.inclusion
  change F.toOrbit.map g ≫ F.toOrbit.map _ = F.toOrbit.map _
  rw [← F.toOrbit.map_comp]
  congr 1
  apply Subtype.ext
  ext x
  exact hg x

theorem alperinStronglyGenerated_centric_aut {P : F.Object}
    (hP : F.IsCentric P.subgroup) (a : P ≅ P) :
    F.AlperinStronglyGenerated a.hom := by
  intro A B hAP hBP g hg
  apply AlperinGenerated.centricRestriction (F.toOrbit.map g) hP (F.toOrbit.mapIso a)
    (F.toOrbit.map (F.inclusion hAP)) (F.toOrbit.map (F.inclusion hBP))
  · change F.toOrbit.map _ ≫ F.toOrbit.map _ = F.toOrbit.map _
    rw [← F.toOrbit.map_comp]
    rfl
  · change F.toOrbit.map _ ≫ F.toOrbit.map _ = F.toOrbit.map _
    rw [← F.toOrbit.map_comp]
    rfl
  · change F.toOrbit.map _ ≫ F.toOrbit.map _ = F.toOrbit.map _ ≫ F.toOrbit.map _
    rw [← F.toOrbit.map_comp, ← F.toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    ext x
    exact hg x

theorem alperinStronglyGenerated_comp {P Q R : F.Object} {f : P ⟶ Q} {g : Q ⟶ R}
    (hf : F.AlperinStronglyGenerated f) (hg : F.AlperinStronglyGenerated g) :
    F.AlperinStronglyGenerated (f ≫ g) := by
  intro A B hAP hBR k hk
  let f₀ := F.inclusion hAP ≫ f
  let I : F.Object := ⟨F.imageSubgroup f₀⟩
  let e : A ≅ I := F.imageIso f₀
  let l : I ⟶ B := e.inv ≫ k
  have he : AlperinGenerated F.centricProperty F.topOrbit F.toTop
      (F.toOrbit.map e.hom) := hf hAP (F.image_le f₀) e.hom (fun _ => rfl)
  have hl : AlperinGenerated F.centricProperty F.topOrbit F.toTop
      (F.toOrbit.map l) := by
    apply hg (F.image_le f₀) hBR l
    intro x
    have heq : (f.val ⟨(e.inv.val x).val, hAP (e.inv.val x).property⟩).val = x.val := by
      have h := congrArg (fun m : I ⟶ I => (m.val x).val) e.inv_hom_id
      exact h
    change (k.val (e.inv.val x)).val = _
    rw [hk]
    change (g.val (f.val _)).val = _
    congr 2
    exact Subtype.ext heq
  have hcomp := AlperinGenerated.comp (F.toOrbit.map e.hom) (F.toOrbit.map l) he hl
  have hekl : e.hom ≫ l = k := by
    change e.hom ≫ (e.inv ≫ k) = k
    simp
  simpa only [← F.toOrbit.map_comp, hekl] using hcomp

end Sharpness.FusionSystem
