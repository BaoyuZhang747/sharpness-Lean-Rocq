import Sharpness.CentricSubchainConjugacy
import Mathlib.CategoryTheory.Category.Preorder

/-! The manuscript's actual normalizer indexing category. Objects are
fusion-conjugacy classes of nonempty strict centric chains. There is
exactly one arrow from a chain to a conjugate of a subchain, and no
other arrows. The orientation is the one in Yalcin Definition 10.1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def NormalizerCategory := Quotient (CentricChain.conjugacySetoid (F := F))

def normalizerClass (σ : F.CentricChain) : F.NormalizerCategory := Quotient.mk _ σ

def normalizerRelation (a b : F.NormalizerCategory) : Prop :=
  Quotient.liftOn₂ a b CentricChain.IsSubconjugate (fun _ _ _ _ c d =>
    propext (CentricChain.IsSubconjugate.congr c d))

instance normalizerPreorder : Preorder F.NormalizerCategory where
  le := F.normalizerRelation
  le_refl a := Quotient.inductionOn a CentricChain.IsSubconjugate.refl
  le_trans a b c := Quotient.inductionOn₃ a b c
    (fun _ _ _ h k => h.trans k)

instance normalizerCategory : SmallCategory F.NormalizerCategory :=
  Preorder.smallCategory _

instance normalizerHomSubsingleton (a b : F.NormalizerCategory) : Subsingleton (a ⟶ b) :=
  Preorder.subsingleton_hom a b

theorem normalizerClass_eq_iff (σ τ : F.CentricChain) :
    F.normalizerClass σ = F.normalizerClass τ ↔ CentricChain.Conjugate σ τ :=
  Quotient.eq

theorem normalizerClass_le_iff (σ τ : F.CentricChain) :
    F.normalizerClass σ ≤ F.normalizerClass τ ↔ CentricChain.IsSubconjugate σ τ := Iff.rfl

theorem normalizerClass_hom_iff (σ τ : F.CentricChain) :
    Nonempty (F.normalizerClass σ ⟶ F.normalizerClass τ) ↔
      CentricChain.IsSubconjugate σ τ :=
  ⟨fun ⟨h⟩ => leOfHom h, fun h => ⟨homOfLE h⟩⟩

def normalizerSubchainArrow (σ : F.CentricChain) (m : ℕ)
    (e : Fin (m + 1) ↪o Fin (σ.length + 1)) :
    F.normalizerClass σ ⟶ F.normalizerClass (σ.subchain m e) :=
  homOfLE ⟨m, e, ⟨CentricChain.Conjugacy.refl _⟩⟩

def normalizerLength : F.NormalizerCategory → ℕ :=
  Quotient.lift (fun σ => σ.length) (fun _ _ h => CentricChain.conjugate_length_eq h)

@[simp] theorem normalizerLength_class (σ : F.CentricChain) :
    F.normalizerLength (F.normalizerClass σ) = σ.length := rfl

theorem normalizerLength_antitone : Antitone F.normalizerLength := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro σ τ h
  exact CentricChain.IsSubconjugate.length_le h

theorem normalizerLength_arrow {a b : F.NormalizerCategory} (f : a ⟶ b) :
    F.normalizerLength b ≤ F.normalizerLength a :=
  F.normalizerLength_antitone (leOfHom f)

end Sharpness.FusionSystem
