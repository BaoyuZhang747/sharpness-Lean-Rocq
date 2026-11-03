import Sharpness.Unconditional.PuigMaximalSpans
import Lean.Elab.Tactic.Omega

/-! The descending-rank induction in Puig's maximal-extension argument.
The concrete fusion-system input is a common normalizer extension, which
increases both intermediate source ranks. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.PuigSpan
open CategoryTheory
variable {C : Type u} [Category.{u} C] {P Q : C}

def Factor.inv {A B : PuigSpan P Q} (f : A.Factor B) [IsIso f.hom] : B.Factor A where
  hom := CategoryTheory.inv f.hom
  left_fac := by rw [← f.left_fac, IsIso.inv_hom_id_assoc]
  right_fac := by rw [← f.right_fac, IsIso.inv_hom_id_assoc]

/-- The diagram used in the normalizer induction, with both new sources
strictly larger than the old common source. -/
structure GrowthAmalgamation (rank : C → ℕ) {X A B : PuigSpan P Q}
    (f : X.Factor A) (g : X.Factor B) where
  Y : PuigSpan P Q
  Z : PuigSpan P Q
  D : PuigSpan P Q
  a : X.Factor Y
  b : X.Factor Z
  c : Y.Factor A
  d : Z.Factor B
  e : Y.Factor D
  h : Z.Factor D
  growY : rank X.apex < rank Y.apex
  growZ : rank X.apex < rank Z.apex
  facA : a.hom ≫ c.hom = f.hom
  facB : b.hom ≫ d.hom = g.hom
  agree : a.hom ≫ e.hom = b.hom ≫ h.hom

/-- Any two maximal extensions of one span are isomorphic by a map
commuting with the prescribed incoming factors. -/
theorem maximal_factor_alignment [Finite C] [∀ X Y : C, Finite (X ⟶ Y)]
    (rank : C → ℕ) (bound : ℕ) (rank_bound : ∀ X, rank X ≤ bound)
    (rank_mono : ∀ {X Y : C} (f : X ⟶ Y), rank X ≤ rank Y)
    (iso_of_rank_eq : ∀ {X Y : C} (f : X ⟶ Y), rank X = rank Y → IsIso f)
    (amalgamate : ∀ {X A B : PuigSpan P Q} (f : X.Factor A) (g : X.Factor B),
      ¬ IsIso f.hom → ¬ IsIso g.hom → Nonempty (GrowthAmalgamation rank f g))
    {X A B : PuigSpan P Q} (hA : A.Maximal) (hB : B.Maximal)
    (f : X.Factor A) (g : X.Factor B) :
    ∃ k : A.Factor B, f.hom ≫ k.hom = g.hom := by
  classical
  have main : ∀ n : ℕ, ∀ (X : PuigSpan P Q), bound - rank X.apex = n →
      ∀ (A B : PuigSpan P Q), A.Maximal → B.Maximal →
      ∀ (f : X.Factor A) (g : X.Factor B),
        ∃ k : A.Factor B, f.hom ≫ k.hom = g.hom := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hn A B hA hB f g
      by_cases hf : IsIso f.hom
      · letI := hf
        refine ⟨f.inv.comp g, ?_⟩
        change f.hom ≫ (inv f.hom ≫ g.hom) = g.hom
        simp
      have hg : ¬ IsIso g.hom := by
        intro hg
        letI := hg
        let k := g.inv.comp f
        letI := hB A k
        have he : f.hom = g.hom ≫ k.hom := by
          change f.hom = g.hom ≫ (inv g.hom ≫ f.hom)
          simp
        apply hf
        rw [he]
        infer_instance
      obtain ⟨W⟩ := amalgamate f g hf hg
      obtain ⟨E, ⟨j⟩, hE⟩ := exists_maximal_extension rank rank_mono iso_of_rank_eq W.D
      have hy : bound - rank W.Y.apex < n := by
        have hb := rank_bound W.Y.apex
        have hh := W.growY
        omega
      have hz : bound - rank W.Z.apex < n := by
        have hb := rank_bound W.Z.apex
        have hh := W.growZ
        omega
      obtain ⟨u, hu⟩ := ih _ hy W.Y rfl A E hA hE W.c (W.e.comp j)
      obtain ⟨v, hv⟩ := ih _ hz W.Z rfl B E hB hE W.d (W.h.comp j)
      letI := hB E v
      refine ⟨u.comp v.inv, ?_⟩
      have he : f.hom ≫ u.hom = g.hom ≫ v.hom := by
        rw [← W.facA, ← W.facB, Category.assoc, Category.assoc, hu, hv]
        change W.a.hom ≫ (W.e.hom ≫ j.hom) = W.b.hom ≫ (W.h.hom ≫ j.hom)
        rw [← Category.assoc, ← Category.assoc, W.agree]
      change f.hom ≫ (u.hom ≫ inv v.hom) = g.hom
      rw [← Category.assoc, he, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact main _ X rfl A B hA hB f g

end Sharpness.PuigSpan
