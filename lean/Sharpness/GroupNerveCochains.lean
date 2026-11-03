import Sharpness.GroupNerveFaces
import Sharpness.SimplexCochainCoordinates

/-! The actual simplicial cochains of the group nerve are isomorphic
to the native inhomogeneous cochain complex, with arbitrary trivial
module coefficients. Both differentials are retained explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Simplicial Opposite
variable (R G : Type u) [CommRing R] [Group G] (A : ModuleCat.{u} R)

def nerveCochainEquiv (n : ℕ) :
    (((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)).X n ⟶ A) ≃ₗ[R]
      ((Fin n → G) → A) :=
  (simplexCochainEquiv R (nerve (SingleObj G)) A n).trans
    (LinearEquiv.funCongrLeft R A (nerveTupleEquiv G n).symm)

theorem nerveCochainEquiv_apply (n : ℕ)
    (f : ((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)).X n ⟶ A)
    (x : (nerve (SingleObj G)).obj (op ⦋n⦌)) :
    nerveCochainEquiv R G A n f (nerveTuple G n x) =
      simplexCochainEquiv R (nerve (SingleObj G)) A n f x := by
  change simplexCochainEquiv R (nerve (SingleObj G)) A n f
    (tupleNerve G n (nerveTuple G n x)) = _
  rw [tupleNerve_nerveTuple]

theorem nerveCochainEquiv_d (n : ℕ)
    (f : ((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)).X n ⟶ A) :
    nerveCochainEquiv R G A (n+1)
        ((((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)).linearYonedaObj R A).d n (n+1) f) =
      (groupCohomology.inhomogeneousCochains (Rep.trivial R G A)).d n (n+1)
        (nerveCochainEquiv R G A n f) := by
  classical
  funext g
  obtain ⟨x, rfl⟩ := (nerveTupleEquiv G (n+1)).surjective g
  change nerveCochainEquiv R G A (n+1)
      ((((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)).linearYonedaObj R A).d n (n+1) f)
        (nerveTuple G (n+1) x) =
    (groupCohomology.inhomogeneousCochains (Rep.trivial R G A)).d n (n+1)
      (nerveCochainEquiv R G A n f) (nerveTuple G (n+1) x)
  rw [nerveCochainEquiv_apply, simplexCochainEquiv_d,
    groupCohomology.inhomogeneousCochains.d_def]
  change (∑ i : Fin (n+2), (-1 : ℤ)^i.val •
      simplexCochainEquiv R (nerve (SingleObj G)) A n f ((nerve (SingleObj G)).δ i x)) =
    nerveCochainEquiv R G A n f (fun i => nerveTuple G (n+1) x i.succ) +
      ∑ j : Fin (n+1), (-1 : R)^(j.val+1) •
        nerveCochainEquiv R G A n f (Fin.contractNth j (· * ·) (nerveTuple G (n+1) x))
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  congr 1
  · rw [← nerveCochainEquiv_apply, nerveTuple_face_zero]
  · apply Finset.sum_congr rfl
    intro j _
    rw [← nerveCochainEquiv_apply, nerveTuple_face_succ]
    norm_cast

def nerveCochainIso :
    ((nerve (SingleObj G)).chainComplex (ModuleCat.of R R)).linearYonedaObj R A ≅
      groupCohomology.inhomogeneousCochains (Rep.trivial R G A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (nerveCochainEquiv R G A n).toModuleIso) (by
      intro i j hij
      have hj : i+1=j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact (nerveCochainEquiv_d R G A i f).symm)

end Sharpness.OrdinaryCohomology
