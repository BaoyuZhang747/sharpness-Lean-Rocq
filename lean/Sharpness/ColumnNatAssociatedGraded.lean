import Sharpness.ColumnLeadingDifferential
import Sharpness.CochainSubmoduleCokernel
import Sharpness.ColumnFiltrationFunctor
import Sharpness.CochainDifferentialThroughEpi

/-! The actual natural-number associated graded complex has the
leading column as its degreewise module, and its actual differential
corresponds to the signed vertical differential. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnNatAssociatedGraded (p : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  cokernel (totalColumnFilteredMap K (Nat.le_succ p))

def totalColumnNatAssociatedGradedTermIso (p q : ℕ) :
    (totalColumnNatAssociatedGraded K p).X (p+q) ≅ (K.X p).X q :=
  CochainSubmodules.cokernelTermIso
    (fun n => totalColumnFiltration_antitone K n (Nat.le_succ p)) (p+q) ≪≫
      totalColumnLeadingQuotientIso K p q

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatAssociatedGradedTermIso_projection (p q : ℕ) :
    (cokernel.π (totalColumnFilteredMap K (Nat.le_succ p))).f (p+q) ≫
      (totalColumnNatAssociatedGradedTermIso K p q).hom =
        ModuleCat.ofHom (totalColumnLeadingMap K p q) := by
  have hp := CochainSubmodules.cokernelTermIso_projection
    (V := totalColumnSubmodules K (p+1)) (W := totalColumnSubmodules K p)
    (fun n => totalColumnFiltration_antitone K n (Nat.le_succ p)) (p+q)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hp' := congrArg (fun f => f x) hp
  change (totalColumnLeadingQuotientIso K p q).hom
    ((CochainSubmodules.cokernelTermIso
      (V := totalColumnSubmodules K (p+1)) (W := totalColumnSubmodules K p)
      (fun n => totalColumnFiltration_antitone K n (Nat.le_succ p)) (p+q)).hom
        ((cokernel.π (totalColumnFilteredMap K (Nat.le_succ p))).f (p+q) x)) = _
  exact (congrArg (fun y => (totalColumnLeadingQuotientIso K p q).hom y) hp').trans
    (totalColumnLeadingQuotientIso_mk K p q x)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatAssociatedGradedTermIso_d (p q : ℕ) :
    (totalColumnNatAssociatedGraded K p).d (p+q) (p+(q+1)) ≫
      (totalColumnNatAssociatedGradedTermIso K p (q+1)).hom =
    (totalColumnNatAssociatedGradedTermIso K p q).hom ≫
      ((-1 : ℤˣ)^p • (K.X p).d q (q+1)) := by
  apply cochain_d_through_epi
    (cokernel.π (totalColumnFilteredMap K (Nat.le_succ p))) (p+q) (p+(q+1))
    (totalColumnNatAssociatedGradedTermIso K p q).hom
    (totalColumnNatAssociatedGradedTermIso K p (q+1)).hom
    ((-1 : ℤˣ)^p • (K.X p).d q (q+1))
    (ModuleCat.ofHom (totalColumnLeadingMap K p q))
    (ModuleCat.ofHom (totalColumnLeadingMap K p (q+1)))
    (totalColumnNatAssociatedGradedTermIso_projection K p q)
    (totalColumnNatAssociatedGradedTermIso_projection K p (q+1))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hi := congrArg (fun g => g x)
    ((totalColumnFilteredInclusion K p).comm (p+q) (p+(q+1)))
  have he : ((totalColumnFilteredComplex K p).d (p+q) (p+(q+1)) x).val =
      (K.total (ComplexShape.up ℕ)).d (p+q) (p+(q+1)) x.val := hi.symm
  exact (congrArg (fun y => totalSummandProjection K p (q+1) y) he).trans
    (totalColumnLeadingMap_d K p q x)

end Sharpness
