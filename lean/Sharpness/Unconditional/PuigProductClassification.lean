import Sharpness.Unconditional.PuigMaximalInduction

/-! Maximal spans with alignment and trivial stabilizers classify pairs
of morphisms. This constructs the actual finite representable product
decomposition, rather than assuming a categorical product comparison. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory

variable {C : Type u} [Category.{u} C] (P Q : C)

abbrev MaximalPuigSpan := {A : PuigSpan P Q // A.Maximal}

def maximalPuigSpanSetoid : Setoid (MaximalPuigSpan P Q) where
  r A B := Nonempty (A.val.Factor B.val)
  iseqv :=
    { refl := fun A => ⟨PuigSpan.Factor.id A.val⟩
      symm := by
        intro A B h
        obtain ⟨f⟩ := h
        letI := A.property B.val f
        exact ⟨f.inv⟩
      trans := by
        intro A B D hAB hBD
        obtain ⟨f⟩ := hAB
        obtain ⟨g⟩ := hBD
        exact ⟨f.comp g⟩ }

abbrev MaximalPuigSpanIndex := Quotient (maximalPuigSpanSetoid P Q)

def maximalPuigSpanRepresentative (i : MaximalPuigSpanIndex P Q) : PuigSpan P Q := i.out.val

theorem maximalPuigSpanRepresentative_maximal (i : MaximalPuigSpanIndex P Q) :
    (maximalPuigSpanRepresentative P Q i).Maximal := i.out.property

variable [Finite C] [∀ X Y : C, Finite (X ⟶ Y)]

def productDecompositionOfMaximalSpans
    (extensions : ∀ A : PuigSpan P Q, ∃ B : PuigSpan P Q,
      Nonempty (A.Factor B) ∧ B.Maximal)
    (alignment : ∀ {X A B : PuigSpan P Q}, A.Maximal → B.Maximal →
      ∀ (f : X.Factor A) (g : X.Factor B), ∃ k : A.Factor B, f.hom ≫ k.hom = g.hom)
    (rigidity : ∀ (A : PuigSpan P Q), A.Maximal → ∀ f : A.Factor A, f.hom = 𝟙 A.apex) :
    ProductDecomposition P Q where
  Index := MaximalPuigSpanIndex P Q
  finiteIndex := inferInstance
  apex i := (maximalPuigSpanRepresentative P Q i).apex
  left i := (maximalPuigSpanRepresentative P Q i).left
  right i := (maximalPuigSpanRepresentative P Q i).right
  bijective X := by
    constructor
    · rintro ⟨i, f⟩ ⟨j, g⟩ heq
      let A := maximalPuigSpanRepresentative P Q i
      let B := maximalPuigSpanRepresentative P Q j
      let U : PuigSpan P Q := { apex := X, left := f ≫ A.left, right := f ≫ A.right }
      let uf : U.Factor A := { hom := f, left_fac := rfl, right_fac := rfl }
      let ug : U.Factor B :=
        { hom := g, left_fac := (congrArg Prod.fst heq).symm,
          right_fac := (congrArg Prod.snd heq).symm }
      obtain ⟨k, hk⟩ := alignment (maximalPuigSpanRepresentative_maximal P Q i)
        (maximalPuigSpanRepresentative_maximal P Q j) uf ug
      have hij : i = j := by
        calc
          i = Quotient.mk _ i.out := (Quotient.out_eq i).symm
          _ = Quotient.mk _ j.out := Quotient.sound ⟨k⟩
          _ = j := Quotient.out_eq j
      subst j
      have hk₁ : k.hom = 𝟙 A.apex := rigidity A i.out.property k
      have hfg : f = g := by
        change f ≫ k.hom = g at hk
        rw [hk₁] at hk
        exact (Category.comp_id f).symm.trans hk
      cases hfg
      rfl
    · rintro ⟨f, g⟩
      let U : PuigSpan P Q := { apex := X, left := f, right := g }
      obtain ⟨B, ⟨h⟩, hB⟩ := extensions U
      let i : MaximalPuigSpanIndex P Q := Quotient.mk _ ⟨B, hB⟩
      have hi : Nonempty (B.Factor (maximalPuigSpanRepresentative P Q i)) :=
        Quotient.exact (Quotient.out_eq i).symm
      obtain ⟨k⟩ := hi
      exact ⟨⟨i, (h.comp k).hom⟩, Prod.ext (h.comp k).left_fac (h.comp k).right_fac⟩

end Sharpness
