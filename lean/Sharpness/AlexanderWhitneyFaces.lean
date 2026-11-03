import Sharpness.BisimplicialChains

/-! Concrete front and back simplex maps for the Alexander–Whitney
component. They retain horizontal vertices 0,...,p and vertical
vertices p,...,n, respectively. In horizontal degree zero the
vertical map is the identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite

def alexanderWhitneyFront (p q n : ℕ) (h : p+q=n) : ⦋p⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.subinterval 0 p (by omega)

def alexanderWhitneyBack (p q n : ℕ) (h : p+q=n) : ⦋q⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.subinterval p q (by omega)

theorem alexanderWhitneyFront_apply (p q n : ℕ) (h : p+q=n) (i : Fin (p+1)) :
    ((alexanderWhitneyFront p q n h).toOrderHom i).val = i.val := rfl

theorem alexanderWhitneyBack_apply (p q n : ℕ) (h : p+q=n) (i : Fin (q+1)) :
    ((alexanderWhitneyBack p q n h).toOrderHom i).val = i.val+p := rfl

theorem alexanderWhitneyFront_zero (n : ℕ) (h : 0+n=n) :
    alexanderWhitneyFront 0 n n h = SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 :=
  SimplexCategory.Hom.ext_zero_left _ _ rfl

theorem alexanderWhitneyBack_zero (n : ℕ) (h : 0+n=n) :
    alexanderWhitneyBack 0 n n h = 𝟙 ⦋n⦌ := by
  ext i : 3
  apply Fin.ext
  rfl

def alexanderWhitneySimplex (X : SimplicialObject SSet.{u})
    (p q n : ℕ) (h : p+q=n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) : (X.obj (op ⦋p⦌)).obj (op ⦋q⦌) :=
  (X.map (alexanderWhitneyFront p q n h).op).app (op ⦋q⦌)
    ((X.obj (op ⦋n⦌)).map (alexanderWhitneyBack p q n h).op x)

theorem alexanderWhitneySimplex_zero (X : SimplicialObject SSet.{u})
    (n : ℕ) (h : 0+n=n) (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    alexanderWhitneySimplex X 0 n n h x =
      (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op).app (op ⦋n⦌) x := by
  simp only [alexanderWhitneySimplex, alexanderWhitneyFront_zero,
    alexanderWhitneyBack_zero, op_id, (X.obj (op ⦋n⦌)).map_id]
  rfl

end Sharpness
