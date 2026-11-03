(** The actual short exact sequence C(A intersection B) -> C(A)+C(B) -> C_small(A,B). *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex ChainShortExact SimplicialSet SimplicialSubcomplex
  SimplicialChains SimplicialChainsMaps SingularSet SingularCohomology SingularSmallChains
  TopologicalCategory SingularChainExcisionSubspaces SingularChainExcisionSubspacesLattice
  SingularChainExcisionSubspacesExact SingularExcisionSequenceMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPChainShortExact DPSimplicialSet DPSimplicialSubcomplex
  DPSimplicialChains DPSimplicialChainMaps DPSingularSet DPSingularCohomology DPSingularSmallChains
  DPTopological DPSingularChainExcisionSubspaces DPSingularChainExcisionSubspacesLattice
  DPSingularChainExcisionSubspacesExact DPSingularExcisionSequenceMaps.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPSingularExcisionSequence.
Section Sequence.
Variable Real : realType.
Variable R : pzRingType.
Variable X : topologicalType.
Variables A B : set X.
Let LA := landing_subcomplex Real A.
Let LB := landing_subcomplex Real B.
Let SA := singular_chains Real R (subset_space A).
Let SB := singular_chains Real R (subset_space B).
Let SI := singular_chains Real R (subset_space (A `&` B)).
Let SC := @small_chains Real X bool (binary_cover A B) R.
Let GA := chains R (subcomplex_set LA).
Let GB := chains R (subcomplex_set LB).
Let GI := chains R (subcomplex_set (subcomplex_intersection LA LB)).
Let GU := chains R (subcomplex_set (subcomplex_union LA LB)).
Let it := intersection_to Real R A B.
Let ifr := intersection_from Real R A B.
Let st := sum_to Real R A B.
Let sfr := sum_from Real R A B.
Let ut := union_to Real R A B.
Let ufr := union_from Real R A B.
Let gf := intersection_sum R LA LB.
Let gg := sum_union R LA LB.
Let gs := subcomplex_union_short_exact R LA LB.

Definition subspace_intersection_sum : chain_map SI (binary_chains SA SB) :=
  chain_composition (chain_composition it gf) sfr.
Definition subspace_sum_small : chain_map (binary_chains SA SB) SC :=
  chain_composition (chain_composition st gg) ufr.

Lemma subspace_intersection_sum_at n x :
  chain_map_at subspace_intersection_sum n x =
  chain_map_at sfr n (chain_map_at gf n (chain_map_at it n x)).
Proof. reflexivity. Qed.
Lemma subspace_sum_small_at n x :
  chain_map_at subspace_sum_small n x =
  chain_map_at ufr n (chain_map_at gg n (chain_map_at st n x)).
Proof. reflexivity. Qed.

Theorem subspace_sequence_short_exact :
  chain_short_exact subspace_intersection_sum subspace_sum_small.
Proof.
constructor.
- move=> n a b h.
  have h1 := congr1 (chain_map_at st n) h.
  rewrite !subspace_intersection_sum_at !sum_to_from in h1.
  have h2 := @exact_injective R GI (binary_chains GA GB) GU gf gg gs n _ _ h1.
  have h3 := congr1 (chain_map_at ifr n) h2.
  by rewrite !intersection_from_to in h3.
- move=> n x.
  rewrite subspace_sum_small_at subspace_intersection_sum_at sum_to_from.
  rewrite (@exact_composite R GI (binary_chains GA GB) GU gf gg gs n) linear0.
  reflexivity.
- move=> n x h.
  have h1 := congr1 (chain_map_at ut n) h.
  rewrite subspace_sum_small_at union_to_from linear0 in h1.
  case: (@exact_kernel R GI (binary_chains GA GB) GU gf gg gs n _ h1) => c hc.
  exists (chain_map_at ifr n c).
  by rewrite subspace_intersection_sum_at intersection_to_from hc sum_from_to.
- move=> n y.
  case: (@exact_surjective R GI (binary_chains GA GB) GU gf gg gs n (chain_map_at ut n y)) => z hz.
  exists (chain_map_at sfr n z).
  by rewrite subspace_sum_small_at sum_to_from hz union_from_to.
Qed.

Definition intersection_left_inclusion : hom topological_category (subset_space (A `&` B)) (subset_space A) :=
  subset_map (fun x h => proj1 h).
Definition intersection_right_inclusion : hom topological_category (subset_space (A `&` B)) (subset_space B) :=
  subset_map (fun x h => proj2 h).

Definition literal_intersection_sum_at n (x : chain_term SI n) : chain_term (binary_chains SA SB) n :=
  (chain_map_at (singular_chain_map Real R intersection_left_inclusion) n x,
  - chain_map_at (singular_chain_map Real R intersection_right_inclusion) n x).
Arguments literal_intersection_sum_at n x : clear implicits.
Lemma literal_intersection_sum_linear n : linear (literal_intersection_sum_at n).
Proof.
move=> r a b; change ((chain_map_at (singular_chain_map Real R intersection_left_inclusion) n (r *: a + b),
 - chain_map_at (singular_chain_map Real R intersection_right_inclusion) n (r *: a + b)) =
 (r *: chain_map_at (singular_chain_map Real R intersection_left_inclusion) n a +
 chain_map_at (singular_chain_map Real R intersection_left_inclusion) n b,
 r *: (- chain_map_at (singular_chain_map Real R intersection_right_inclusion) n a) -
 chain_map_at (singular_chain_map Real R intersection_right_inclusion) n b)).
by rewrite !linearP scalerN.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (literal_intersection_sum_at n)
  (@literal_intersection_sum_linear n).

Lemma subspace_intersection_sum_literal n (x : chain_term SI n) :
  chain_map_at subspace_intersection_sum n x = literal_intersection_sum_at n x.
Proof.
apply (free_lift_ext (g := chain_map_at subspace_intersection_sum n)
  (h := (literal_intersection_sum_at n : {linear _ -> _}))).
move=> s; rewrite subspace_intersection_sum_at.
change ((map_at R (landing_to_subspace Real A) n
  (map_at R (subcomplex_map (fun n s (h : member (subcomplex_intersection LA LB) n s) => proj1 h)) n
  (map_at R (nat_comp (subspace_to_landing Real (A `&` B))
  (subcomplex_map (@intersection_landing_to Real X A B))) n (free_basis R s))),
  map_at R (landing_to_subspace Real B) n
  (- map_at R (subcomplex_map (fun n s (h : member (subcomplex_intersection LA LB) n s) => proj2 h)) n
  (map_at R (nat_comp (subspace_to_landing Real (A `&` B))
  (subcomplex_map (@intersection_landing_to Real X A B))) n (free_basis R s)))) =
 (map_at R (singular_map Real intersection_left_inclusion) n (free_basis R s),
 - map_at R (singular_map Real intersection_right_inclusion) n (free_basis R s))).
rewrite linearN !map_at_basis.
congr (_, _).
- congr (free_basis R _); apply topological_hom_ext => t; apply val_inj; reflexivity.
- congr (- free_basis R _); apply topological_hom_ext => t; apply val_inj; reflexivity.
Qed.

End Sequence.
End DPSingularExcisionSequence.
