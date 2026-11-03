import Sharpness.Saturation

/-! A centric subgroup is automatically fully centralized: its ambient
centralizer is its own center, whose order is preserved by isomorphisms. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem

variable {S : Type u} [Group S]

def centerEquivAmbientCentralizer (Q : Subgroup S)
    (hQ : Subgroup.centralizer (Q : Set S) ≤ Q) :
    Subgroup.center Q ≃* Subgroup.centralizer (Q : Set S) where
  toFun x := ⟨x.val.val, by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp x.property) ⟨y, hy⟩)⟩
  invFun x := ⟨⟨x.val, hQ x.property⟩, by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp x.property) y.val y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [Finite S] (F : FusionSystem S)

theorem centric_fullyCentralized {Q : Subgroup S} (hQ : F.IsCentric Q) :
    F.FullyCentralized Q := by
  have hself : Subgroup.centralizer (Q : Set S) ≤ Q := by
    simpa only [inf_top_eq] using hQ Q le_top (MulEquiv.refl Q) (F.id_mem Q)
  intro R e he
  have hR : Subgroup.centralizer (R : Set S) ≤ R := by
    simpa only [inf_top_eq] using hQ R le_top e he
  have hc := Nat.card_congr
    (((centerEquivAmbientCentralizer Q hself).symm.trans
      (Subgroup.centerCongr e)).trans (centerEquivAmbientCentralizer R hR)).toEquiv
  exact hc.ge

end Sharpness.FusionSystem
