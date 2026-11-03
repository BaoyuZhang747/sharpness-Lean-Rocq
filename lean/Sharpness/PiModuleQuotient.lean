import Sharpness.KernelQuotientIso
import Mathlib.LinearAlgebra.Pi

/-! Quotients commute with arbitrary products of modules. Both the
kernel and the simultaneous representative lift are explicit; no
finiteness restriction on the indexing type is introduced. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {R ι : Type u} [CommRing R] (V : ι → Type u)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (P : ∀ i, Submodule R (V i))

def piModuleQuotientMap : (∀ i, V i) →ₗ[R] ∀ i, V i ⧸ P i :=
  LinearMap.pi (fun i => (P i).mkQ.comp (LinearMap.proj i))

theorem piModuleQuotientMap_ker :
    (piModuleQuotientMap V P).ker = Submodule.pi Set.univ P := by
  ext x
  constructor
  · intro hx
    intro i _
    exact (Submodule.Quotient.mk_eq_zero (P i)).mp (congrFun hx i)
  · intro hx
    funext i
    exact (Submodule.Quotient.mk_eq_zero (P i)).mpr (hx i (Set.mem_univ i))

theorem piModuleQuotientMap_surjective : Function.Surjective (piModuleQuotientMap V P) := by
  intro y
  choose x hx using fun i => (P i).mkQ_surjective (y i)
  exact ⟨x, funext hx⟩

def piModuleQuotientIso :
    ModuleCat.of R ((∀ i, V i) ⧸ Submodule.pi Set.univ P) ≅
      ModuleCat.of R (∀ i, V i ⧸ P i) :=
  quotientIsoOfKer (piModuleQuotientMap V P) _ (piModuleQuotientMap_ker V P)
    (piModuleQuotientMap_surjective V P)

theorem piModuleQuotientIso_mk (x : ∀ i, V i) :
    (piModuleQuotientIso V P).hom (Submodule.Quotient.mk x) =
      fun i => Submodule.Quotient.mk (x i) :=
  quotientIsoOfKer_mk _ _ _ _ x

end Sharpness
