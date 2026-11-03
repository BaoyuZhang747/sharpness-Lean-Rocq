(** Plain nonnegative downward complexes of arbitrary modules.
    Exactness and projectivity are not fields of this definition. *)
From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Module DPChainComplex.
Section Complexes.
Variable R : pzRingType.

Record chain_complex := ChainComplex {
  chain_term : nat -> lmodType R;
  chain_d : forall n, {linear chain_term n.+1 -> chain_term n};
  chain_d2 : forall n x, chain_d n (chain_d n.+1 x) = 0
}.

Definition cycle (C : chain_complex) n : chain_term C n -> Prop :=
  match n as k return chain_term C k -> Prop with
  | 0%N => fun _ => True
  | k.+1 => fun x => chain_d C k x = 0
  end.

Definition boundary (C : chain_complex) n (x : chain_term C n) : Prop :=
  exists y, chain_d C n y = x.

Arguments cycle _ _ _ : clear implicits.
Arguments boundary _ _ _ : clear implicits.

Lemma boundary_cycle (C : chain_complex) n (x : chain_term C n) :
  boundary C n x -> cycle C n x.
Proof.
case: n x => [|n] x /=.
- by move=> _.
- by move=> [y <-]; exact: chain_d2.
Qed.

Record chain_map (C D : chain_complex) := ChainMap {
  chain_map_at : forall n, {linear chain_term C n -> chain_term D n};
  chain_map_commutes : forall n x,
    chain_d D n (chain_map_at n.+1 x) = chain_map_at n (chain_d C n x)
}.

Definition chain_identity (C : chain_complex) : chain_map C C.
Proof.
refine (@ChainMap C C (fun n =>
  (idfun : {linear chain_term C n -> chain_term C n})) _).
by move=> n x.
Defined.

Definition chain_composition (C D E : chain_complex)
    (f : chain_map C D) (g : chain_map D E) : chain_map C E.
Proof.
refine (@ChainMap C E (fun n =>
  (chain_map_at g n \o chain_map_at f n :
    {linear chain_term C n -> chain_term E n})) _).
by move=> n x; rewrite /= !chain_map_commutes.
Defined.

Lemma chain_map_cycle (C D : chain_complex) (f : chain_map C D)
    n (x : chain_term C n) : cycle C n x -> cycle D n (chain_map_at f n x).
Proof.
case: n x => [|n] x /=.
- by move=> _.
- by move=> hx; rewrite chain_map_commutes hx linear0.
Qed.

Lemma chain_map_boundary (C D : chain_complex) (f : chain_map C D)
    n (x : chain_term C n) : boundary C n x -> boundary D n (chain_map_at f n x).
Proof.
move=> [y <-]; exists (chain_map_at f n.+1 y).
exact: chain_map_commutes.
Qed.

Record chain_homotopy (C D : chain_complex) (f g : chain_map C D) := ChainHomotopy {
  chain_homotopy_at : forall n, {linear chain_term C n -> chain_term D n.+1};
  chain_homotopy_zero : forall x,
    chain_d D 0%N (chain_homotopy_at 0%N x) =
      chain_map_at f 0%N x - chain_map_at g 0%N x;
  chain_homotopy_succ : forall n x,
    chain_d D n.+1 (chain_homotopy_at n.+1 x) +
      chain_homotopy_at n (chain_d C n x) =
        chain_map_at f n.+1 x - chain_map_at g n.+1 x
}.

Arguments chain_homotopy_succ {C D f g} h n x : rename.

Lemma chain_homotopy_boundary (C D : chain_complex) (f g : chain_map C D)
    (h : chain_homotopy f g) n (x : chain_term C n) :
    cycle C n x -> boundary D n (chain_map_at f n x - chain_map_at g n x).
Proof.
case: n x => [|n] x hx.
- exists (chain_homotopy_at h 0%N x). exact: chain_homotopy_zero.
- exists (chain_homotopy_at h n.+1 x).
  have hh := chain_homotopy_succ h n x.
  by rewrite hx linear0 addr0 in hh.
Qed.

Definition acyclic (C : chain_complex) : Prop :=
  forall n x, cycle C n x -> boundary C n x.

End Complexes.
End DPChainComplex.
