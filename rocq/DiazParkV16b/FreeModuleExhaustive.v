(** Finite supports turn literal exhaustive generator ranges into exhaustive
    free-module ranges, with a common stage for every finite chain. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From DiazPark Require Import BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule.
Local Open Scope ring_scope.

Module DPFreeModuleExhaustive.

Lemma finite_sequence_stage (X : eqType) (P : nat -> X -> Prop)
  (hm : forall n m, (n <= m)%N -> forall x, P n x -> P m x)
  (hc : forall x, exists n, P n x) (s : seq X) :
  exists n, forall x, x \in s -> P n x.
Proof.
elim: s => [|x s [n hn]].
- exists 0%N; by move=> x; rewrite in_nil.
- have [m hmX] := hc x; exists (maxn n m) => y.
  rewrite in_cons => /orP[/eqP ->|hy].
  + exact (@hm m (maxn n m) (leq_maxr n m) x hmX).
  + exact (@hm n (maxn n m) (leq_maxl n m) y (hn y hy)).
Qed.

Section Free.
Variable R : pzRingType.

Lemma free_map_lift_supported (X Y : Type) (f : X -> Y) (a : free_module R Y)
  (h : forall y, y \in free_support a -> exists x, f x = y) :
  exists b, free_map R f b = a.
Proof.
have hs : forall s : seq (generator_type Y),
  (forall y, y \in s -> exists x, f x = y) ->
  exists b, free_map R f b = \sum_(y <- s) (free_coefficient a y : R) *: free_basis R y.
  elim=> [|y s ih] hs.
  - exists 0; by rewrite linear0 big_nil.
  - have [x hx] := hs y (mem_head y s).
    have ht : forall z, z \in s -> exists x, f x = z.
      move=> z hz; apply hs; by rewrite in_cons hz orbT.
    have [b hb] := ih ht.
    exists ((free_coefficient a y : R) *: free_basis R x + b).
    by rewrite linearD linearZ free_map_basis hx hb big_cons.
have [b hb] := hs (free_support a) h.
exists b; by rewrite free_basis_generation in hb.
Qed.

Theorem free_map_exhaustive (X : Type) (Y : nat -> Type) (f : forall n, Y n -> X)
  (hm : forall n m, (n <= m)%N -> forall x,
    (exists y, f n y = x) -> exists y, f m y = x)
  (hc : forall x, exists n y, f n y = x) (a : free_module R X) :
  exists n b, free_map R (f n) b = a.
Proof.
have hp : forall x : generator_type X, exists n, exists y, f n y = x := hc.
have [n hn] := @finite_sequence_stage (generator_type X)
  (fun n x => exists y, f n y = x) hm hp (free_support a).
have [b hb] := @free_map_lift_supported (Y n) X (f n) a hn.
by exists n,b.
Qed.
End Free.
End DPFreeModuleExhaustive.
