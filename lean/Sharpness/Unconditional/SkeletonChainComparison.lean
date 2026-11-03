import Sharpness.Unconditional.SmallChainComparisonAlgebra

/-! Native chain comparison through exhaustive injective stages. The proof
uses actual finite-chain lifts and native cycle/boundary criteria, rather than
assuming that singular chains or homology preserve a filtered colimit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w
namespace Sharpness.SkeletonComparison
open CategoryTheory HomologicalComplex ChainCofiber SmallChainComparison
variable {R : Type u} [Ring R] {ι : Type w}
variable {S K : ChainComplex (ModuleCat.{v} R) ℕ}

theorem quasiIso_of_stage_chain_lifts
    (f : S ⟶ K) (A B : ι → ChainComplex (ModuleCat.{v} R) ℕ)
    (a : ∀ k, A k ⟶ S) (b : ∀ k, B k ⟶ K) (g : ∀ k, A k ⟶ B k)
    (hw : ∀ k, a k ≫ f = g k ≫ b k)
    (ha : ∀ k n, Function.Injective ((a k).f n))
    (hb : ∀ k n, Function.Injective ((b k).f n))
    (hg : ∀ k, QuasiIso (g k))
    (htarget : ∀ n (y : K.X n), ∃ k, ∃ z : (B k).X n, (b k).f n z = y)
    (hpair : ∀ n (x : S.X n) (y : K.X (n+1)),
      ∃ k, ∃ xs : (A k).X n, ∃ ys : (B k).X (n+1),
        (a k).f n xs = x ∧ (b k).f (n+1) ys = y) : QuasiIso f := by
  apply (quasiIso_iff_cycle_conditions f).mpr
  intro n
  constructor
  · intro x hx hy
    obtain ⟨y, hy⟩ := hy
    obtain ⟨k, xs, ys, hxs, hys⟩ := hpair n x y
    have hxc : Cycle (A k) n xs := cycle_of_injective_map (a k) (ha k) n xs (by
      rw [hxs]
      exact hx)
    have hbound : (B k).d (n+1) n ys = (g k).f n xs := by
      apply hb k n
      calc
        (b k).f n ((B k).d (n+1) n ys) = K.d (n+1) n ((b k).f (n+1) ys) :=
          chainMap_apply_d (b k) (n+1) n ys
        _ = K.d (n+1) n y := congrArg (K.d (n+1) n) hys
        _ = f.f n x := hy
        _ = f.f n ((a k).f n xs) := congrArg (f.f n) hxs.symm
        _ = (b k).f n ((g k).f n xs) :=
          congrArg (fun h : A k ⟶ K => (h.f n).hom xs) (hw k)
    obtain ⟨z, hz⟩ := ((quasiIso_iff_cycle_conditions (g k)).mp (hg k) n).1
      xs hxc ⟨ys, hbound⟩
    refine ⟨(a k).f (n+1) z, ?_⟩
    rw [← chainMap_apply_d, hz, hxs]
  · intro y hy
    obtain ⟨k, ys, hys⟩ := htarget n y
    have hyc : Cycle (B k) n ys := cycle_of_injective_map (b k) (hb k) n ys (by
      rw [hys]
      exact hy)
    obtain ⟨xs, hxs, z, hz⟩ := ((quasiIso_iff_cycle_conditions (g k)).mp (hg k) n).2 ys hyc
    refine ⟨(a k).f n xs, cycle_map (a k) n xs hxs, (b k).f (n+1) z, ?_⟩
    calc
      f.f n ((a k).f n xs) + K.d (n+1) n ((b k).f (n+1) z) =
          (b k).f n ((g k).f n xs) + K.d (n+1) n ((b k).f (n+1) z) := by
        exact congrArg (fun t => t + K.d (n+1) n ((b k).f (n+1) z))
          (congrArg (fun h : A k ⟶ K => (h.f n).hom xs) (hw k))
      _ = (b k).f n ((g k).f n xs + (B k).d (n+1) n z) := by
        rw [map_add, chainMap_apply_d]
      _ = (b k).f n ys := congrArg ((b k).f n) hz
      _ = y := hys

end Sharpness.SkeletonComparison
