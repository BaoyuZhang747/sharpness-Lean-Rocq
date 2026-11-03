(** Eventual membership under an invariant linear map, including finite supports. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule.
Local Open Scope ring_scope.

Module DPEventualSubmodule.
Section Iterates.
Variable R : pzRingType.
Variable V : lmodType R.
Variable f : {linear V -> V}.

Fixpoint linear_iter k : {linear V -> V} :=
  match k with 0%N => (idfun : {linear V -> V})
  | k.+1 => (f \o linear_iter k : {linear V -> V}) end.

Lemma linear_iter_add k l x : linear_iter (k + l) x = linear_iter k (linear_iter l x).
Proof. by elim: k => [|k ih] //; rewrite addSn /= ih. Qed.

Variable N : module_subspace V.
Variable hf : forall x, N x -> N (f x).

Lemma linear_iter_preserves k x : N x -> N (linear_iter k x).
Proof. move=> hx; elim: k => [|k ih] //; exact: hf ih. Qed.

Lemma linear_iter_mem_of_le k l x : (k <= l)%N -> N (linear_iter k x) -> N (linear_iter l x).
Proof.
move=> h hx; rewrite -(subnK h) linear_iter_add; exact: linear_iter_preserves hx.
Qed.

Definition eventual_subspace : module_subspace V.
Proof.
refine (@ModuleSubspace R V (fun x => exists k, N (linear_iter k x)) _ _ _).
- exists 0%N; exact: subspace_zero.
- move=> x y [k hk] [l hl]; exists (k+l)%N; rewrite linearD; apply: subspace_add.
  + exact: (@linear_iter_mem_of_le k (k+l)%N x (leq_addr l k) hk).
  + exact: (@linear_iter_mem_of_le l (k+l)%N y (leq_addl k l) hl).
- move=> a x [k hk]; exists k; rewrite linearZ; exact: subspace_scale hk.
Defined.

Theorem eventual_finite (xs : seq V)
    (hxs : forall x, x \in xs -> eventual_subspace x) :
  exists k, forall l, (k <= l)%N -> forall x, x \in xs -> N (linear_iter l x).
Proof.
elim: xs hxs => [|x xs ih] hxs.
- exists 0%N; by move=> l hl x; rewrite in_nil.
- have [k hk] := hxs x (mem_head x xs).
  have ht : forall y, y \in xs -> eventual_subspace y.
    move=> y hy; apply: hxs; by rewrite in_cons hy orbT.
  have [m hm] := ih ht.
  exists (k+m)%N => l hl y; rewrite in_cons => /orP[/eqP ->|hy].
  + apply: (linear_iter_mem_of_le _ hk); exact: (leq_trans (leq_addr m k) hl).
  + apply: hm hy; exact: (leq_trans (leq_addl k m) hl).
Qed.
End Iterates.

Section FreeGenerators.
Variable R : pzRingType.
Variable X : Type.
Variable f : {linear free_module R X -> free_module R X}.
Variable N : module_subspace (free_module R X).
Variable hf : forall x, N x -> N (f x).
Variable hb : forall x, exists k, N (linear_iter f k (free_basis R x)).

Theorem eventual_free_chain (x : free_module R X) : exists k, N (linear_iter f k x).
Proof.
change (eventual_subspace hf x).
rewrite -(free_basis_generation x).
elim: (free_support x) => [|y ys ih]; rewrite ?big_nil ?big_cons.
- exact: subspace_zero.
- apply: subspace_add ih; apply: subspace_scale; exact: hb.
Qed.
End FreeGenerators.
End DPEventualSubmodule.
