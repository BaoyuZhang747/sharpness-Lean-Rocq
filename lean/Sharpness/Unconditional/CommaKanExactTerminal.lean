import Sharpness.Unconditional.CommaKanExact

/-! Terminal representatives of costructured-arrow components give exact
right Kan extension on contravariant module diagrams. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {J : Type u} [Category.{u} J] {I : Type u}

/-- Structured arrows to a discrete family are precisely the indexed arrows. -/
def structuredArrowDiscreteEquiv (T : I → J) (X : J) :
    StructuredArrow X (Discrete.functor T) ≃ (Σ i, X ⟶ T i) where
  toFun Y := ⟨Y.right.as, Y.hom⟩
  invFun y := StructuredArrow.mk (T := Discrete.functor T) (Y := Discrete.mk y.1) y.2
  left_inv Y := by
    rcases Y with ⟨⟨⟨⟩⟩, ⟨i⟩, f⟩
    rfl
  right_inv y := by cases y; rfl

/-- A unique arrow from each object to exactly one member is a final family. -/
theorem final_discrete_of_unique_terminal_family (T : I → J)
    (hT : ∀ X, Unique (Σ i, X ⟶ T i)) : (Discrete.functor T).Final where
  out X := by
    letI := hT X
    letI : Nonempty (StructuredArrow X (Discrete.functor T)) :=
      ⟨(structuredArrowDiscreteEquiv T X).symm default⟩
    letI : Subsingleton (StructuredArrow X (Discrete.functor T)) :=
      (structuredArrowDiscreteEquiv T X).injective.subsingleton
    infer_instance

variable {A B : Type u} [Category.{u} A] [Category.{u} B] (L : A ⥤ B)

/-- The opposite terminal representatives, in the comma category for Ran. -/
def oppositeTerminalFamily (b : B) (T : I → CostructuredArrow L b) :
    Discrete I ⥤ StructuredArrow (op b) L.op :=
  (Discrete.opposite I).inverse ⋙ (Discrete.functor T).op ⋙
    (costructuredArrowOpEquivalence L b).functor

theorem oppositeTerminalFamily_initial (b : B) (T : I → CostructuredArrow L b)
    (hT : ∀ X, Unique (Σ i, X ⟶ T i)) : (oppositeTerminalFamily L b T).Initial := by
  letI := final_discrete_of_unique_terminal_family T hT
  dsimp [oppositeTerminalFamily]
  infer_instance

variable (R : Type u) [CommRing R]

/-- Right Kan extension along the opposite functor preserves epimorphisms
when each original comma category has a unique terminal representative. -/
theorem ran_op_preservesEpimorphisms_of_unique_terminal_family
    (I : B → Type u) (T : ∀ b, I b → CostructuredArrow L b)
    (hT : ∀ b X, Unique (Σ i, X ⟶ T b i)) :
    (L.op.ran (H := ModuleCat.{u} R)).PreservesEpimorphisms :=
  ran_preservesEpimorphisms_of_initialDiscrete R L.op (fun b => I b.unop)
    (fun b => oppositeTerminalFamily L b.unop (T b.unop))
    (fun b => oppositeTerminalFamily_initial L b.unop (T b.unop) (hT b.unop))

/-- The same right Kan extension is exact, expressed as homology preservation. -/
theorem ran_op_preservesHomology_of_unique_terminal_family
    (I : B → Type u) (T : ∀ b, I b → CostructuredArrow L b)
    (hT : ∀ b X, Unique (Σ i, X ⟶ T b i)) :
    (L.op.ran (H := ModuleCat.{u} R)).PreservesHomology :=
  ran_preservesHomology_of_initialDiscrete R L.op (fun b => I b.unop)
    (fun b => oppositeTerminalFamily L b.unop (T b.unop))
    (fun b => oppositeTerminalFamily_initial L b.unop (T b.unop) (hT b.unop))

end Sharpness
