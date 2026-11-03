import Sharpness.Unconditional.GroupCohomologyTransferIso

/-! Actual transfer covariance for commutative squares of subgroup
inclusions and group isomorphisms, including literal ambient subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G K S A : Type u} [CommRing R] [Group G] [Group K] [Group S]
  [AddCommGroup A] [Module R A]

theorem transfer_mulEquiv_square [Finite G] [Finite K]
    (H : Subgroup G) (J : Subgroup K) (e : G ≃* K) (eH : H ≃* J)
    (hsq : J.subtype.comp eH.toMonoidHom = e.toMonoidHom.comp H.subtype) (n : ℕ) :
    transfer (R := R) (A := A) H n ≫ pull e.symm.toMonoidHom n =
      pull eH.symm.toMonoidHom n ≫ transfer (R := R) (A := A) J n := by
  have hval (x : H) : ((eH x : J) : K) = e (x : G) :=
    DFunLike.congr_fun hsq x
  have hJ : J = H.map e.toMonoidHom := by
    apply le_antisymm
    · intro x hx
      refine ⟨(eH.symm ⟨x, hx⟩ : G), (eH.symm ⟨x, hx⟩).property, ?_⟩
      exact (hval (eH.symm ⟨x, hx⟩)).symm.trans
        (congrArg Subtype.val (eH.apply_symm_apply ⟨x, hx⟩))
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      change e y ∈ J
      rw [← hval ⟨y, hy⟩]
      exact (eH ⟨y, hy⟩).property
  subst J
  have heH : eH = e.subgroupMap H := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    exact hval x
  rw [heH]
  exact transfer_mulEquiv e H n

theorem subgroupTransfer_mulEquiv_square [Finite S]
    (P Q P' Q' : Subgroup S) (h : P ≤ Q) (h' : P' ≤ Q')
    (eP : P ≃* P') (eQ : Q ≃* Q')
    (hsq : (Subgroup.inclusion h').comp eP.toMonoidHom =
      eQ.toMonoidHom.comp (Subgroup.inclusion h)) (n : ℕ) :
    (pullLinear (R := R) (A := A) eQ.symm.toMonoidHom n).comp
        (subgroupTransfer P Q h n) =
      (subgroupTransfer P' Q' h' n).comp
        (pullLinear (R := R) (A := A) eP.symm.toMonoidHom n) := by
  let a := Subgroup.subgroupOfEquivOfLe h
  let b := Subgroup.subgroupOfEquivOfLe h'
  let eH := a.trans (eP.trans b.symm)
  have hs : (P'.subgroupOf Q').subtype.comp eH.toMonoidHom =
      eQ.toMonoidHom.comp (P.subgroupOf Q).subtype := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact congrArg Subtype.val (DFunLike.congr_fun hsq (a x))
  have he : a.toMonoidHom.comp eH.symm.toMonoidHom =
      eP.symm.toMonoidHom.comp b.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact a.apply_symm_apply (eP.symm (b x))
  have hh : (pull (R := R) (A := A) a.toMonoidHom n ≫
      transfer (P.subgroupOf Q) n) ≫ pull eQ.symm.toMonoidHom n =
        pull eP.symm.toMonoidHom n ≫
          (pull b.toMonoidHom n ≫ transfer (P'.subgroupOf Q') n) := by
    rw [Category.assoc, transfer_mulEquiv_square _ _ eQ eH hs,
      ← Category.assoc, ← pull_comp, he, pull_comp, Category.assoc]
  exact congrArg (fun f : value R P A n ⟶ value R Q' A n => f.hom) hh

end Sharpness.OrdinaryCohomology
