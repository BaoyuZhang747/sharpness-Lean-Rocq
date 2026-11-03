(** Actual chain comparisons for the topological-subspace Mayer--Vietoris sequence. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialSubcomplex
  SimplicialChains SimplicialChainsMaps SingularSet SingularCohomology SingularSmallChains
  TopologicalCategory SingularChainExcisionSubspaces SingularChainExcisionSubspacesLattice
  SingularChainExcisionSubspacesExact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet DPSimplicialSubcomplex
  DPSimplicialChains DPSimplicialChainMaps DPSingularSet DPSingularCohomology DPSingularSmallChains
  DPTopological DPSingularChainExcisionSubspaces DPSingularChainExcisionSubspacesLattice
  DPSingularChainExcisionSubspacesExact.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularExcisionSequenceMaps.
Section BinaryMaps.
Variable R : pzRingType.
Variables C D E F : chain_complex R.
Variables (f : chain_map C E) (g : chain_map D F).
Definition binary_map_at n (x : chain_term (binary_chains C D) n) :
    chain_term (binary_chains E F) n := (chain_map_at f n x.1, chain_map_at g n x.2).
Arguments binary_map_at n x : clear implicits.
Lemma binary_map_at_linear n : linear (binary_map_at n).
Proof. move=> r [a b] [c d]; congr (_, _); exact: linearP. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (binary_map_at n) (@binary_map_at_linear n).
Definition binary_chain_map : chain_map (binary_chains C D) (binary_chains E F).
Proof.
refine (@ChainMap R _ _ (fun n => (binary_map_at n : {linear _ -> _})) _).
move=> n [a b]; change ((chain_d E n (chain_map_at f n.+1 a), chain_d F n (chain_map_at g n.+1 b)) =
 (chain_map_at f n (chain_d C n a), chain_map_at g n (chain_d D n b))).
by rewrite !chain_map_commutes.
Defined.
End BinaryMaps.

Section Maps.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variables A B : set X.
Let SX := singular_set Real X.
Let LA := landing_subcomplex Real A.
Let LB := landing_subcomplex Real B.
Let LI := subcomplex_intersection LA LB.
Let LU := subcomplex_union LA LB.
Let SA := singular_chains Real R (subset_space A).
Let SB := singular_chains Real R (subset_space B).
Let SI := singular_chains Real R (subset_space (A `&` B)).
Let SC := @small_chains Real X bool (binary_cover A B) R.
Let GA := chains R (subcomplex_set LA).
Let GB := chains R (subcomplex_set LB).
Let GI := chains R (subcomplex_set LI).
Let GU := chains R (subcomplex_set LU).

Definition intersection_landing_to : subcomplex_le (landing_subcomplex Real (A `&` B)) LI :=
  fun n s h => conj (fun t => proj1 (h t)) (fun t => proj2 (h t)).
Definition intersection_landing_from : subcomplex_le LI (landing_subcomplex Real (A `&` B)) :=
  fun n s h t => conj (proj1 h t) (proj2 h t).
Definition small_union_to : subcomplex_le (small_subcomplex Real (binary_cover A B)) LU.
Proof. move=> n s [][|] h; [left | right]; exact h. Defined.
Definition small_union_from : subcomplex_le LU (small_subcomplex Real (binary_cover A B)).
Proof. move=> n s [h|h]; [exists true | exists false]; exact h. Defined.

Definition intersection_to : chain_map SI GI := chain_map_of R
  (nat_comp (subspace_to_landing Real (A `&` B)) (subcomplex_map intersection_landing_to)).
Definition intersection_from : chain_map GI SI := chain_map_of R
  (nat_comp (subcomplex_map intersection_landing_from) (landing_to_subspace Real (A `&` B))).
Definition union_to : chain_map SC GU := chain_map_of R (subcomplex_map small_union_to).
Definition union_from : chain_map GU SC := chain_map_of R (subcomplex_map small_union_from).
Definition sum_to : chain_map (binary_chains SA SB) (binary_chains GA GB) :=
  binary_chain_map (subspace_to_landing_chains Real A R) (subspace_to_landing_chains Real B R).
Definition sum_from : chain_map (binary_chains GA GB) (binary_chains SA SB) :=
  binary_chain_map (landing_to_subspace_chains Real A R) (landing_to_subspace_chains Real B R).

Lemma intersection_from_to n (x : chain_term SI n) :
  chain_map_at intersection_from n (chain_map_at intersection_to n x) = x.
Proof.
apply (free_lift_ext (g := (chain_map_at intersection_from n \o chain_map_at intersection_to n : {linear _ -> _}))
  (h := (idfun : {linear chain_term SI n -> chain_term SI n}))).
move=> s.
change (map_at R (nat_comp (subcomplex_map intersection_landing_from) (landing_to_subspace Real (A `&` B))) n
 (map_at R (nat_comp (subspace_to_landing Real (A `&` B)) (subcomplex_map intersection_landing_to)) n (free_basis R s)) = free_basis R s).
rewrite !map_at_basis; congr (free_basis R _).
apply topological_hom_ext => t; apply val_inj; reflexivity.
Qed.

Lemma intersection_to_from n (x : chain_term GI n) :
  chain_map_at intersection_to n (chain_map_at intersection_from n x) = x.
Proof.
apply (free_lift_ext (g := (chain_map_at intersection_to n \o chain_map_at intersection_from n : {linear _ -> _}))
  (h := (idfun : {linear chain_term GI n -> chain_term GI n}))).
move=> s.
change (map_at R (nat_comp (subspace_to_landing Real (A `&` B)) (subcomplex_map intersection_landing_to)) n
 (map_at R (nat_comp (subcomplex_map intersection_landing_from) (landing_to_subspace Real (A `&` B))) n (free_basis R s)) = free_basis R s).
rewrite !map_at_basis; congr (free_basis R _).
apply subcomplex_simplex_ext; apply topological_hom_ext => t; reflexivity.
Qed.

Lemma union_from_to n (x : chain_term SC n) :
  chain_map_at union_from n (chain_map_at union_to n x) = x.
Proof.
apply (free_lift_ext (g := (chain_map_at union_from n \o chain_map_at union_to n : {linear _ -> _}))
  (h := (idfun : {linear chain_term SC n -> chain_term SC n}))).
move=> s.
change (map_at R (subcomplex_map small_union_from) n
 (map_at R (subcomplex_map small_union_to) n (free_basis R s)) = free_basis R s).
rewrite !map_at_basis; congr (free_basis R _); apply subcomplex_simplex_ext; reflexivity.
Qed.

Lemma union_to_from n (x : chain_term GU n) :
  chain_map_at union_to n (chain_map_at union_from n x) = x.
Proof.
apply (free_lift_ext (g := (chain_map_at union_to n \o chain_map_at union_from n : {linear _ -> _}))
  (h := (idfun : {linear chain_term GU n -> chain_term GU n}))).
move=> s.
change (map_at R (subcomplex_map small_union_to) n
 (map_at R (subcomplex_map small_union_from) n (free_basis R s)) = free_basis R s).
rewrite !map_at_basis; congr (free_basis R _); apply subcomplex_simplex_ext; reflexivity.
Qed.

Lemma sum_from_to n (x : chain_term (binary_chains SA SB) n) :
  chain_map_at sum_from n (chain_map_at sum_to n x) = x.
Proof.
case: x => a b; change ((chain_map_at (landing_to_subspace_chains Real A R) n
 (chain_map_at (subspace_to_landing_chains Real A R) n a),
 chain_map_at (landing_to_subspace_chains Real B R) n
 (chain_map_at (subspace_to_landing_chains Real B R) n b)) = (a,b)).
by rewrite !landing_subspace_chainsK.
Qed.

Lemma sum_to_from n (x : chain_term (binary_chains GA GB) n) :
  chain_map_at sum_to n (chain_map_at sum_from n x) = x.
Proof.
case: x => a b; change ((chain_map_at (subspace_to_landing_chains Real A R) n
 (chain_map_at (landing_to_subspace_chains Real A R) n a),
 chain_map_at (subspace_to_landing_chains Real B R) n
 (chain_map_at (landing_to_subspace_chains Real B R) n b)) = (a,b)).
by rewrite !subspace_landing_chainsK.
Qed.

End Maps.
End DPSingularExcisionSequenceMaps.
