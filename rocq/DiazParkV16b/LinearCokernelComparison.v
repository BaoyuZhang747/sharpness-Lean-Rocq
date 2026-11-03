(** Actual cokernel comparison, including the terminal degree of an exact sequence. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure HomologicalModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.
Module DPLinearCokernelComparison.
Section Comparison.
Variable R : pzRingType.
Variables A B C A' B' C' : lmodType R.
Variables (f : {linear A -> B}) (g : {linear B -> C})
  (f' : {linear A' -> B'}) (g' : {linear B' -> C'}).
Variables (u : {linear A -> A'}) (v : {linear B -> B'}) (w : {linear C -> C'}).
Variables (hf : forall x, v (f x) = f' (u x))
  (hg : forall x, w (g x) = g' (v x)).
Variables (hs : linear_exact f g) (hs' : linear_exact f' g').
Variable hgs : forall x, exists y, g y = x.
Variable hgs' : forall x, exists y, g' y = x.

Theorem cokernel_injective (hus : forall x, exists y, u y = x) (hvi : injective v) : injective w.
Proof.
have ker : forall x, w x = 0 -> x = 0.
  move=> x hx; have [b hb] := hgs x.
  have hv : g' (v b) = 0 by rewrite -hg hb hx.
  have [a' ha'] := proj1 (hs' (v b)) hv.
  have [a ha] := hus a'.
  have eb : b = f a by apply hvi; rewrite hf ha ha'.
  rewrite -hb eb; apply/(hs (f a)); by exists a.
move=> x y h; apply/subr0_eq; apply ker; by rewrite linearB h subrr.
Qed.

Theorem cokernel_surjective (hvs : forall x, exists y, v y = x) :
  forall x, exists y, w y = x.
Proof.
move=> x; have [b' hb'] := hgs' x; have [b hb] := hvs b'.
exists (g b); by rewrite hg hb hb'.
Qed.

Definition cokernel_iso (hus : forall x, exists y, u y = x)
    (hvi : injective v) (hvs : forall x, exists y, v y = x) :
    @isomorphism (module_category R) C C' :=
  @linear_bijection_iso R C C' w (cokernel_injective hus hvi) (cokernel_surjective hvs).
End Comparison.
End DPLinearCokernelComparison.
