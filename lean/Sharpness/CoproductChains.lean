import Sharpness.ModuleDirectSumMaps
import Sharpness.SingularCochains

/-! The concrete direct-sum complex of a family of chain complexes.
Every differential and inclusion is constructed, with no finiteness
assumption on the family. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {ι : Type u}
    (K : ι → ChainComplex (ModuleCat.{u} R) ℕ)

def coproductChainsDifferential (n : ℕ) :
    moduleDirectSum (fun i => (K i).X (n+1)) ⟶ moduleDirectSum (fun i => (K i).X n) :=
  moduleDirectSumDesc (fun i => (K i).X (n+1))
    (fun i => (K i).d (n+1) n ≫ moduleDirectSumInclusion (fun i => (K i).X n) i)

@[reassoc]
theorem coproductChainsDifferential_inclusion (n : ℕ) (i : ι) :
    moduleDirectSumInclusion (fun i => (K i).X (n+1)) i ≫ coproductChainsDifferential K n =
      (K i).d (n+1) n ≫ moduleDirectSumInclusion (fun i => (K i).X n) i :=
  moduleDirectSumInclusion_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem coproductChainsDifferential_comp (n : ℕ) :
    coproductChainsDifferential K (n+1) ≫ coproductChainsDifferential K n = 0 := by
  apply moduleDirectSum_hom_ext
  intro i
  rw [← Category.assoc, coproductChainsDifferential_inclusion,
    Category.assoc, coproductChainsDifferential_inclusion,
    ← Category.assoc, (K i).d_comp_d, zero_comp, comp_zero]

def coproductChains : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => moduleDirectSum (fun i => (K i).X n))
    (coproductChainsDifferential K) (coproductChainsDifferential_comp K)

def coproductChainsInclusion (i : ι) : K i ⟶ coproductChains K :=
  ChainComplex.ofHom (fun n => moduleDirectSumInclusion (fun i => (K i).X n) i) (by
    intro n
    simp only [coproductChains, ChainComplex.of_d]
    exact coproductChainsDifferential_inclusion K n i)

end Sharpness
