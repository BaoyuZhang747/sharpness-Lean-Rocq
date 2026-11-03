(** The genuine intersection--sum--union short exact sequence of simplicial chains. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainShortExact SimplicialSet
  SimplicialSubcomplex SimplicialChains SimplicialChainsMaps FreeModuleBinaryUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainShortExact
  DPSimplicialSet DPSimplicialSubcomplex DPSimplicialChains DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPSingularChainExcisionSubspacesExact.
Section BinaryComplex.
Variable R : pzRingType.
Variables C D : chain_complex R.
Definition binary_chain_term n : lmodType R :=
  [the lmodType R of (chain_term C n * chain_term D n)%type].
Definition binary_chain_d n (x : binary_chain_term n.+1) : binary_chain_term n :=
  (chain_d C n x.1, chain_d D n x.2).
Arguments binary_chain_d n x : clear implicits.
Lemma binary_chain_d_linear n : linear (binary_chain_d n).
Proof. move=> r [a b] [c d]; congr (_, _); exact: linearP. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (binary_chain_d n) (@binary_chain_d_linear n).
Definition binary_chains : chain_complex R.
Proof.
refine (@ChainComplex R binary_chain_term (fun n => (binary_chain_d n : {linear _ -> _})) _).
by move=> n [a b]; change ((chain_d C n (chain_d C n.+1 a), chain_d D n (chain_d D n.+1 b)) = (0,0)); rewrite !chain_d2.
Defined.
End BinaryComplex.

Section SubcomplexUnion.
Variable R : pzRingType.
Variable X : simplicial_set.
Variables A B : subcomplex X.
Let AB := subcomplex_intersection A B.
Let AU := subcomplex_union A B.
Let CA := chains R (subcomplex_set A).
Let CB := chains R (subcomplex_set B).
Let CI := chains R (subcomplex_set AB).
Let CU := chains R (subcomplex_set AU).

Definition intersection_left := chain_map_of R
  (subcomplex_map (fun n s (h : member AB n s) => proj1 h)).
Definition intersection_right := chain_map_of R
  (subcomplex_map (fun n s (h : member AB n s) => proj2 h)).
Definition union_left := chain_map_of R
  (subcomplex_map (fun n s (h : member A n s) => (or_introl h : member AU n s))).
Definition union_right := chain_map_of R
  (subcomplex_map (fun n s (h : member B n s) => (or_intror h : member AU n s))).

Definition intersection_sum_at n (x : chain_term CI n) : chain_term (binary_chains CA CB) n :=
  (chain_map_at intersection_left n x, - chain_map_at intersection_right n x).
Arguments intersection_sum_at n x : clear implicits.
Lemma intersection_sum_at_linear n : linear (intersection_sum_at n).
Proof.
move=> r a b; change ((chain_map_at intersection_left n (r *: a + b),
  - chain_map_at intersection_right n (r *: a + b)) =
  (r *: chain_map_at intersection_left n a + chain_map_at intersection_left n b,
  r *: (- chain_map_at intersection_right n a) + (- chain_map_at intersection_right n b))).
by rewrite !linearP scalerN.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (intersection_sum_at n) (@intersection_sum_at_linear n).

Definition intersection_sum : chain_map CI (binary_chains CA CB).
Proof.
refine (@ChainMap R CI (binary_chains CA CB) (fun n => (intersection_sum_at n : {linear _ -> _})) _).
move=> n x; change ((chain_d CA n (chain_map_at intersection_left n.+1 x),
  chain_d CB n (- chain_map_at intersection_right n.+1 x)) =
  (chain_map_at intersection_left n (chain_d CI n x),
  - chain_map_at intersection_right n (chain_d CI n x))).
by rewrite linearN !chain_map_commutes.
Defined.

Definition sum_union_at n (x : chain_term (binary_chains CA CB) n) : chain_term CU n :=
  chain_map_at union_left n x.1 + chain_map_at union_right n x.2.
Arguments sum_union_at n x : clear implicits.
Lemma sum_union_at_linear n : linear (sum_union_at n).
Proof.
move=> r [a b] [c d]; change
  (chain_map_at union_left n (r *: a + c) + chain_map_at union_right n (r *: b + d) =
  r *: (chain_map_at union_left n a + chain_map_at union_right n b) +
  (chain_map_at union_left n c + chain_map_at union_right n d)).
by rewrite !linearP scalerDr addrACA.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (sum_union_at n) (@sum_union_at_linear n).

Definition sum_union : chain_map (binary_chains CA CB) CU.
Proof.
refine (@ChainMap R (binary_chains CA CB) CU (fun n => (sum_union_at n : {linear _ -> _})) _).
move=> n [a b]; change
  (chain_d CU n (chain_map_at union_left n.+1 a + chain_map_at union_right n.+1 b) =
   chain_map_at union_left n (chain_d CA n a) + chain_map_at union_right n (chain_d CB n b)).
by rewrite linearD !chain_map_commutes.
Defined.

Theorem subcomplex_union_short_exact : chain_short_exact intersection_sum sum_union.
Proof.
constructor.
- move=> n a b h.
  have e := congr1 (@fst (chain_term CA n) (chain_term CB n)) h.
  exact (@DPFreeModuleBinaryUnion.inter_left_injective R (simplex X n)
    (member A n) (member B n) a b e).
- move=> n x.
  change (chain_map_at union_left n (chain_map_at intersection_left n x) +
    chain_map_at union_right n (- chain_map_at intersection_right n x) = 0).
  rewrite linearN.
  have h := @DPFreeModuleBinaryUnion.intersection_square R (simplex X n)
    (member A n) (member B n) x.
  change (chain_map_at union_left n (chain_map_at intersection_left n x) =
    chain_map_at union_right n (chain_map_at intersection_right n x)) in h.
  by rewrite h subrr.
- move=> n [a b] h.
  case: (@DPFreeModuleBinaryUnion.union_kernel R (simplex X n)
    (member A n) (member B n) a b h) => c [hc hd].
  exists c; change ((chain_map_at intersection_left n c, - chain_map_at intersection_right n c) = (a,b)).
  congr (_, _); [exact hc | exact hd].
- move=> n c.
  case: (@DPFreeModuleBinaryUnion.union_surjective R (simplex X n)
    (member A n) (member B n) c) => a [b h].
  exists (a,b); exact h.
Qed.

End SubcomplexUnion.
End DPSingularChainExcisionSubspacesExact.
