(** The actual connecting map on native downward-chain homology quotients. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModules CategoryModuleLinear ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainShortExact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainShortExact.
Local Open Scope ring_scope.

Module DPChainConnecting.
Section Connecting.
Variable R : pzRingType.
Variables A B C : chain_complex R.
Variables (f : chain_map A B) (g : chain_map B C).
Variable s : chain_short_exact f g.

Definition connecting_lift n (z : cycle_module C n.+1) : chain_term B n.+1 :=
  proj1_sig (constructive_indefinite_description (@exact_surjective R A B C f g s n.+1 (val z))).
Lemma connecting_lift_spec n (z : cycle_module C n.+1) :
  chain_map_at g n.+1 (connecting_lift z) = val z.
Proof. exact: (proj2_sig (constructive_indefinite_description (@exact_surjective R A B C f g s n.+1 (val z)))). Qed.

Lemma connecting_lift_kernel n (z : cycle_module C n.+1) :
  chain_map_at g n (chain_d B n (connecting_lift z)) = 0.
Proof. rewrite -chain_map_commutes connecting_lift_spec; exact: (submodule_val_mem z). Qed.

Definition connecting_preimage n (z : cycle_module C n.+1) : chain_term A n :=
  proj1_sig (constructive_indefinite_description
    (@exact_kernel R A B C f g s n _ (connecting_lift_kernel z))).
Lemma connecting_preimage_spec n (z : cycle_module C n.+1) :
  chain_map_at f n (connecting_preimage z) = chain_d B n (connecting_lift z).
Proof. exact: (proj2_sig (constructive_indefinite_description
    (@exact_kernel R A B C f g s n _ (connecting_lift_kernel z)))). Qed.

Lemma connecting_preimage_cycle n (z : cycle_module C n.+1) :
  @cycle R A n (connecting_preimage z).
Proof.
case: n z => [|n] z; first exact I.
apply: (@exact_injective R A B C f g s n).
rewrite linear0 -chain_map_commutes connecting_preimage_spec; exact: chain_d2.
Qed.

Definition connecting_cycle n (z : cycle_module C n.+1) : cycle_module A n :=
  cycle_of_cycle (connecting_preimage_cycle z).
Definition connecting_class n (z : cycle_module C n.+1) : homology A n :=
  quotient_pi (boundaries_in_cycles A n) (connecting_cycle z).

Lemma connecting_class_solution n (z : cycle_module C n.+1)
    (b : chain_term B n.+1) (a : cycle_module A n)
    (hb : chain_map_at g n.+1 b = val z)
    (ha : chain_map_at f n (val a) = chain_d B n b) :
  connecting_class z = quotient_pi (boundaries_in_cycles A n) a.
Proof.
apply/homology_pi_eq.
have hk : chain_map_at g n.+1 (connecting_lift z - b) = 0.
  by rewrite linearB connecting_lift_spec hb subrr.
have [u hu] := @exact_kernel R A B C f g s n.+1 _ hk.
exists u; apply: (@exact_injective R A B C f g s n).
change (chain_map_at f n (chain_d A n u) = chain_map_at f n (connecting_preimage z - val a)).
by rewrite -chain_map_commutes hu !linearB connecting_preimage_spec ha.
Qed.

Lemma connecting_class_linear n : linear (@connecting_class n).
Proof.
move=> r z w; rewrite -linearP.
apply: (@connecting_class_solution n (r *: z + w)
  (r *: connecting_lift z + connecting_lift w)
  (r *: connecting_cycle z + connecting_cycle w)).
- by rewrite linearP !connecting_lift_spec; change (r *: val z + val w = val (r *: z + w)); rewrite linearP.
- change (chain_map_at f n (r *: connecting_preimage z + connecting_preimage w) =
    chain_d B n (r *: connecting_lift z + connecting_lift w)).
  by rewrite !linearP !connecting_preimage_spec.
Qed.

Definition connecting_class_hom n : module_hom
    [the lmodType R of cycle_module C n.+1] [the lmodType R of homology A n] :=
  exist _ (@connecting_class n) (@connecting_class_linear n).

Lemma connecting_class_boundary n (z : cycle_module C n.+1) :
  boundaries_in_cycles C n.+1 z -> connecting_class z = 0.
Proof.
move=> [c hc]; have [b hb] := @exact_surjective R A B C f g s n.+2 c.
have he := @connecting_class_solution n z (chain_d B n.+1 b) 0.
have hg : chain_map_at g n.+1 (chain_d B n.+1 b) = val z.
  by rewrite -chain_map_commutes hb hc.
have hf : chain_map_at f n (val (0 : cycle_module A n)) = chain_d B n (chain_d B n.+1 b).
  by rewrite !linear0 chain_d2.
rewrite (he hg hf); exact: linear0.
Qed.

Definition connecting_map n : {linear homology C n.+1 -> homology A n} :=
  @quotient_lift R (cycle_module C n.+1) (boundaries_in_cycles C n.+1)
    [the lmodType R of homology A n]
    (module_hom_to_linear (connecting_class_hom n)) (@connecting_class_boundary n).

Lemma connecting_map_pi n (z : cycle_module C n.+1) :
  connecting_map n (quotient_pi (boundaries_in_cycles C n.+1) z) = connecting_class z.
Proof. exact: quotient_lift_pi. Qed.
End Connecting.
End DPChainConnecting.
