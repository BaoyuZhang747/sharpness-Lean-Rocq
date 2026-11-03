import Sharpness.SubsystemCentric
import Sharpness.Saturation

/-! Actual elementary abelian objects and centralizer subsystems.
The only imported structural facts are AKO I.5.3/I.5.5 and Yalcin 8.11.
Neither Mackey restriction nor any higher-limit vanishing occurs in these
reference records. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (p : ℕ)

def elementaryProperty (E : F.Object) : Prop :=
  E.subgroup ≠ ⊥ ∧ (∀ x y : E.subgroup, x*y = y*x) ∧
    (∀ x : E.subgroup, x^p = 1) ∧ F.FullyCentralized E.subgroup

/-- The manuscript's F^e, with actual fusion homomorphisms, rather than
orbit morphisms. Full centralization is part of the object predicate. -/
abbrev ElementaryCategory := ObjectProperty.FullSubcategory (F.elementaryProperty p)

def centralizerGroup (E : F.ElementaryCategory p) : Subgroup S :=
  Subgroup.centralizer (E.obj.subgroup : Set S)

def elementaryInCentralizer (E : F.ElementaryCategory p) : Subgroup (F.centralizerGroup p E) :=
  E.obj.subgroup.subgroupOf (F.centralizerGroup p E)

theorem elementary_le_centralizer (E : F.ElementaryCategory p) :
    E.obj.subgroup ≤ F.centralizerGroup p E := by
  intro x hx
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  exact congrArg (fun z : E.obj.subgroup => z.val) (E.property.2.1 ⟨y, hy⟩ ⟨x, hx⟩)

variable [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

/-- AKO Definition I.5.3 and Theorem I.5.5 (K=1). The defining extension
fixes E pointwise. Joins inside C_S(E) correspond to the actual products
PE in the reference, since E is central in C_S(E). -/
structure AKOCentralizerInput (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) where
  system : FusionSystem (F.centralizerGroup p E)
  hom_iff : ∀ {P Q : Subgroup (F.centralizerGroup p E)} (f : P →* Q),
    system.IsHom f ↔ F.IsHom (ambientHom (F.centralizerGroup p E) f) ∧
      ∃ g : (P ⊔ F.elementaryInCentralizer p E : Subgroup (F.centralizerGroup p E)) →*
          (Q ⊔ F.elementaryInCentralizer p E : Subgroup (F.centralizerGroup p E)),
        F.IsHom (ambientHom (F.centralizerGroup p E) g) ∧
        (∀ x : P, (g ⟨x.val, (show P ≤ P ⊔ F.elementaryInCentralizer p E from le_sup_left) x.property⟩).val = (f x).val) ∧
        (∀ z : F.elementaryInCentralizer p E,
          (g ⟨z.val, (show F.elementaryInCentralizer p E ≤ P ⊔ F.elementaryInCentralizer p E from le_sup_right) z.property⟩).val = z.val)
  AKO_I_5_5 : system.Saturated p

variable {p hS sat}

def AKOCentralizerInput.embedding {E : F.ElementaryCategory p}
    (C : F.AKOCentralizerInput p hS sat E) : F.SubsystemEmbedding (F.centralizerGroup p E) C.system where
  hom_mem f hf := ((C.hom_iff f).mp hf).1

/-- Exactly Yalcin Lemma 8.11 for the abelian fully-centralized E. -/
structure YalcinCentralizerCentricInput (E : F.ElementaryCategory p)
    (C : F.AKOCentralizerInput p hS sat E) : Prop where
  lemma_8_11 : ∀ P : Subgroup (F.centralizerGroup p E),
    (C.system.IsCentric P ↔ F.IsCentric (ambientSubgroup (F.centralizerGroup p E) P)) ∧
      (C.system.IsCentric P → F.elementaryInCentralizer p E ≤ P)

def YalcinCentralizerCentricInput.centric {E : F.ElementaryCategory p}
    {C : F.AKOCentralizerInput p hS sat E} (Y : F.YalcinCentralizerCentricInput E C) :
    ∀ P : Subgroup (F.centralizerGroup p E),
      C.system.IsCentric P → F.IsCentric (ambientSubgroup (F.centralizerGroup p E) P) :=
  fun P hc => ((Y.lemma_8_11 P).1).mp hc

end Sharpness.FusionSystem
