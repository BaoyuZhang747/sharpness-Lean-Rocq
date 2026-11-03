import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! Reversing nerve strings identifies the nerve of the opposite category
with the opposite simplicial set. All simplicial operators are respected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u

namespace Sharpness
open CategoryTheory Simplicial Opposite

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

private theorem stringMap_heq {n : ℕ} (s : ComposableArrows C n)
    {a b a' b' : Fin (n+1)} (f : a ⟶ b) (g : a' ⟶ b')
    (ha : a = a') (hb : b = b') : HEq (s.map f) (s.map g) := by
  subst a'; subst b'; cases Subsingleton.elim f g; rfl

private theorem stringMap_op_heq {n : ℕ} (s : ComposableArrows C n)
    {a b a' b' : Fin (n+1)} (f : a ⟶ b) (g : a' ⟶ b')
    (ha : a = a') (hb : b = b') : HEq (s.map f).op (s.map g).op := by
  subst a'; subst b'; cases Subsingleton.elim f g; rfl

private theorem stringMap_unop_heq {n : ℕ} (s : ComposableArrows Cᵒᵖ n)
    {a b a' b' : Fin (n+1)} (f : a ⟶ b) (g : a' ⟶ b')
    (ha : a = a') (hb : b = b') : HEq (s.map f).unop (s.map g).unop := by
  subst a'; subst b'; cases Subsingleton.elim f g; rfl

def nerveStringReverse {n : ℕ} (s : ComposableArrows C n) :
    ComposableArrows Cᵒᵖ n where
  obj i := op (s.obj i.rev)
  map f := (s.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).op
  map_id i := by simp
  map_comp f g := by
    rw [← CategoryTheory.op_comp, ← s.map_comp]
    congr 2

def nerveStringReverseUnop {n : ℕ} (s : ComposableArrows Cᵒᵖ n) :
    ComposableArrows C n where
  obj i := unop (s.obj i.rev)
  map f := (s.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom f)))).unop
  map_id i := by simp
  map_comp f g := by
    rw [← CategoryTheory.unop_comp, ← s.map_comp]
    congr 2

@[simp] theorem nerveStringReverseUnop_reverse {n : ℕ} (s : ComposableArrows C n) :
    nerveStringReverseUnop (nerveStringReverse s) = s := by
  refine CategoryTheory.Functor.hext (fun i => congrArg s.obj (Fin.rev_rev i)) ?_
  intro i j f
  exact stringMap_heq s _ f (Fin.rev_rev i) (Fin.rev_rev j)

@[simp] theorem nerveStringReverse_reverseUnop {n : ℕ}
    (s : ComposableArrows Cᵒᵖ n) :
    nerveStringReverse (nerveStringReverseUnop s) = s := by
  refine CategoryTheory.Functor.hext (fun i => congrArg s.obj (Fin.rev_rev i)) ?_
  intro i j f
  exact stringMap_heq s _ f (Fin.rev_rev i) (Fin.rev_rev j)

def nerveOppositeToOp : nerve Cᵒᵖ ⟶ (nerve C).op where
  app _ := ↾nerveStringReverseUnop
  naturality {p q} f := by
    ext s
    refine CategoryTheory.Functor.hext (fun i => ?_) ?_
    · change unop (s.obj (f.unop.toOrderHom i.rev)) =
        unop (s.obj ((f.unop.toOrderHom i.rev).rev.rev))
      simp
    intro i j g
    apply stringMap_unop_heq s
    · exact (Fin.rev_rev _).symm
    · exact (Fin.rev_rev _).symm

def nerveOpToOpposite : (nerve C).op ⟶ nerve Cᵒᵖ where
  app _ := ↾nerveStringReverse
  naturality {p q} f := by
    ext s
    refine CategoryTheory.Functor.hext (fun i => ?_) ?_
    · change op (s.obj ((f.unop.toOrderHom i.rev.rev).rev)) =
        op (s.obj ((f.unop.toOrderHom i).rev))
      simp
    intro i j g
    apply stringMap_op_heq s
    · exact congrArg (fun k => (f.unop.toOrderHom k).rev) (Fin.rev_rev j)
    · exact congrArg (fun k => (f.unop.toOrderHom k).rev) (Fin.rev_rev i)

def nerveOppositeSimplicialIso (C : Type u) [Category.{v} C] :
    nerve Cᵒᵖ ≅ (nerve C).op where
  hom := nerveOppositeToOp
  inv := nerveOpToOpposite
  hom_inv_id := by ext p s; exact nerveStringReverse_reverseUnop s
  inv_hom_id := by ext p s; exact nerveStringReverseUnop_reverse s

theorem nerveOppositeSimplicialIso_naturality (F : C ⥤ D) :
    nerveMap F.op ≫ (nerveOppositeSimplicialIso D).hom =
      (nerveOppositeSimplicialIso C).hom ≫ SSet.opFunctor.map (nerveMap F) := by
  ext p s
  rfl

end Sharpness
