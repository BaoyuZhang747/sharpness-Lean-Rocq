import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Signed reversal on alternating face-map complexes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w v u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Simplicial Opposite
open AlgebraicTopology

def nerveReversalSign : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1)^(n+1) * nerveReversalSign n

theorem negOnePow_mul_self (n : ℕ) : (-1:ℤ)^n * (-1:ℤ)^n = 1 := by
  rw [← mul_pow]
  simp

@[simp] theorem nerveReversalSign_mul_self (n : ℕ) :
    nerveReversalSign n * nerveReversalSign n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [nerveReversalSign]
    calc
      _ = ((-1:ℤ)^(n+1) * (-1:ℤ)^(n+1)) *
        (nerveReversalSign n * nerveReversalSign n) := by ac_rfl
      _ = 1 := by rw [negOnePow_mul_self, ih, one_mul]

theorem negOnePow_rev {n : ℕ} (i : Fin (n+2)) :
    (-1:ℤ)^i.rev.val = (-1:ℤ)^(n+1) * (-1:ℤ)^i.val := by
  have hi : i.rev.val + i.val = n+1 := by
    simp only [Fin.val_rev]
    omega
  calc
    _ = (-1:ℤ)^i.rev.val * ((-1:ℤ)^i.val * (-1:ℤ)^i.val) := by
      rw [negOnePow_mul_self, mul_one]
    _ = (-1:ℤ)^(i.rev.val + i.val) * (-1:ℤ)^i.val := by rw [pow_add, mul_assoc]
    _ = _ := by rw [hi]

variable {A : Type u} [Category.{v} A] [Preadditive A]

theorem alternatingFaceMapComplex_op_d (X : SimplicialObject A) (n : ℕ) :
    AlternatingFaceMapComplex.objD (SimplicialObject.opFunctor.obj X) n =
      (-1:ℤ)^(n+1) • AlternatingFaceMapComplex.objD X n := by
  have hd (i : Fin (n+2)) : (SimplicialObject.opFunctor.obj X).δ i = X.δ i.rev := by
    have h := SimplicialObject.opFunctor_obj_δ X i
    change (SimplicialObject.opFunctor.obj X).δ i =
      (𝟙 (X.obj (op ⦋n+1⦌))) ≫ X.δ i.rev ≫ (𝟙 (X.obj (op ⦋n⦌))) at h
    simpa only [Category.id_comp, Category.comp_id] using h
  simp only [AlternatingFaceMapComplex.objD, hd]
  rw [← (Equiv.sum_comp Fin.revPerm (fun i : Fin (n+2) => (-1:ℤ)^i.val • X.δ i.rev))]
  simp only [Fin.revPerm_apply, Fin.rev_rev, negOnePow_rev, mul_smul, Finset.smul_sum]

def alternatingFaceMapComplexOpHom (X : SimplicialObject A) :
    AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj X) ⟶
      AlternatingFaceMapComplex.obj X :=
  ChainComplex.ofHom (fun n => nerveReversalSign n • 𝟙 _) (fun n => by
    simp only [AlternatingFaceMapComplex.obj, ChainComplex.of_d,
      zsmul_comp, Category.id_comp, comp_zsmul, Category.comp_id,
      alternatingFaceMapComplex_op_d, smul_smul, nerveReversalSign]
    rw [mul_comm])

def alternatingFaceMapComplexOpInv (X : SimplicialObject A) :
    AlternatingFaceMapComplex.obj X ⟶
      AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj X) :=
  ChainComplex.ofHom (fun n => nerveReversalSign n • 𝟙 _) (fun n => by
    simp only [AlternatingFaceMapComplex.obj, ChainComplex.of_d,
      zsmul_comp, Category.id_comp, comp_zsmul, Category.comp_id,
      alternatingFaceMapComplex_op_d, smul_smul, nerveReversalSign]
    congr 1
    calc
      _ = nerveReversalSign n * ((-1:ℤ)^(n+1) * (-1:ℤ)^(n+1)) := by ac_rfl
      _ = _ := by rw [negOnePow_mul_self, mul_one])

def alternatingFaceMapComplexOpIso (X : SimplicialObject A) :
    AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj X) ≅
      AlternatingFaceMapComplex.obj X where
  hom := alternatingFaceMapComplexOpHom X
  inv := alternatingFaceMapComplexOpInv X
  hom_inv_id := by
    ext n
    change (nerveReversalSign n • 𝟙 _) ≫ (nerveReversalSign n • 𝟙 _) = 𝟙 _
    simp [smul_smul]
  inv_hom_id := by
    ext n
    change (nerveReversalSign n • 𝟙 _) ≫ (nerveReversalSign n • 𝟙 _) = 𝟙 _
    simp [smul_smul]

theorem alternatingFaceMapComplexOpIso_naturality {X Y : SimplicialObject A}
    (f : X ⟶ Y) :
    AlternatingFaceMapComplex.map (SimplicialObject.opFunctor.map f) ≫
      (alternatingFaceMapComplexOpIso Y).hom =
    (alternatingFaceMapComplexOpIso X).hom ≫ AlternatingFaceMapComplex.map f := by
  ext n
  change f.app (op ⦋n⦌) ≫ (nerveReversalSign n • 𝟙 (Y.obj (op ⦋n⦌))) =
    (nerveReversalSign n • 𝟙 (X.obj (op ⦋n⦌))) ≫ f.app (op ⦋n⦌)
  simp

end Sharpness
