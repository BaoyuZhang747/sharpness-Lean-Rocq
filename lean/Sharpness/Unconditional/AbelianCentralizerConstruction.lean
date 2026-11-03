import Sharpness.Unconditional.CentralizerConstruction

/-! The actual centralizer fusion system at any abelian subgroup. Neither
nontriviality nor an exponent condition is part of the construction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] (F : FusionSystem S)

/-- An arbitrary abelian subgroup, with no elementary or centralization condition. -/
structure AbelianCentralizerData (F : FusionSystem S) where
  subgroup : Subgroup S
  abelian : ∀ x y : subgroup, x * y = y * x

def abelianCentralizerGroup (E : F.AbelianCentralizerData) : Subgroup S :=
  Subgroup.centralizer (E.subgroup : Set S)

def abelianInCentralizer (E : F.AbelianCentralizerData) :
    Subgroup (F.abelianCentralizerGroup E) :=
  E.subgroup.subgroupOf (F.abelianCentralizerGroup E)

theorem abelian_le_centralizer (E : F.AbelianCentralizerData) :
    E.subgroup ≤ F.abelianCentralizerGroup E := by
  intro x hx
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  exact congrArg (fun z : E.subgroup => z.val) (E.abelian ⟨y, hy⟩ ⟨x, hx⟩)

theorem abelianInCentralizer_ambient (E : F.AbelianCentralizerData) :
    ambientSubgroup (F.abelianCentralizerGroup E) (F.abelianInCentralizer E) = E.subgroup := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro x hx
    exact ⟨⟨x, F.abelian_le_centralizer E hx⟩, hx, rfl⟩

def abelianCentralizerSystem (E : F.AbelianCentralizerData) :
    FusionSystem (F.abelianCentralizerGroup E) :=
  (F.subgroupRestriction (F.abelianCentralizerGroup E)).centralizingSystem
    (F.abelianInCentralizer E) (by
      intro z hz
      apply Subgroup.mem_center_iff.mpr
      intro t
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp t.property) z.val hz).symm)

theorem abelianCentralizerSystem_hom_iff (E : F.AbelianCentralizerData)
    {P Q : Subgroup (F.abelianCentralizerGroup E)} (f : P →* Q) :
    (F.abelianCentralizerSystem E).IsHom f ↔
      F.IsHom (ambientHom (F.abelianCentralizerGroup E) f) ∧
      ∃ g : (P ⊔ F.abelianInCentralizer E : Subgroup (F.abelianCentralizerGroup E)) →*
          (Q ⊔ F.abelianInCentralizer E : Subgroup (F.abelianCentralizerGroup E)),
        F.IsHom (ambientHom (F.abelianCentralizerGroup E) g) ∧
        (∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f x).val) ∧
        (∀ z : F.abelianInCentralizer E,
          (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val) := Iff.rfl

theorem abelianCentralizerSystem_central (E : F.AbelianCentralizerData) :
    (F.abelianCentralizerSystem E).CentralSubgroup (F.abelianInCentralizer E) :=
  (F.subgroupRestriction (F.abelianCentralizerGroup E)).centralizingSystem_central _ _

/-- Centralizer at the specified abelian subgroup, with no bundled extra hypotheses. -/
def centralizerOfAbelian (E : Subgroup S) (hab : ∀ x y : E, x * y = y * x) :
    FusionSystem (Subgroup.centralizer (E : Set S)) :=
  F.abelianCentralizerSystem ⟨E, hab⟩

theorem centralizerOfAbelian_hom_iff (E : Subgroup S)
    (hab : ∀ x y : E, x * y = y * x)
    {P Q : Subgroup (Subgroup.centralizer (E : Set S))} (f : P →* Q) :
    (F.centralizerOfAbelian E hab).IsHom f ↔
      F.IsHom (ambientHom (Subgroup.centralizer (E : Set S)) f) ∧
      ∃ g : (P ⊔ E.subgroupOf (Subgroup.centralizer (E : Set S)) :
          Subgroup (Subgroup.centralizer (E : Set S))) →*
        (Q ⊔ E.subgroupOf (Subgroup.centralizer (E : Set S)) :
          Subgroup (Subgroup.centralizer (E : Set S))),
        F.IsHom (ambientHom (Subgroup.centralizer (E : Set S)) g) ∧
        (∀ x : P, (g ⟨x.val, Subgroup.mem_sup_left x.property⟩).val = (f x).val) ∧
        (∀ z : E.subgroupOf (Subgroup.centralizer (E : Set S)),
          (g ⟨z.val, Subgroup.mem_sup_right z.property⟩).val = z.val) := Iff.rfl

theorem centralizerOfAbelian_central (E : Subgroup S)
    (hab : ∀ x y : E, x * y = y * x) :
    (F.centralizerOfAbelian E hab).CentralSubgroup
      (E.subgroupOf (Subgroup.centralizer (E : Set S))) :=
  F.abelianCentralizerSystem_central ⟨E, hab⟩

end Sharpness.FusionSystem
