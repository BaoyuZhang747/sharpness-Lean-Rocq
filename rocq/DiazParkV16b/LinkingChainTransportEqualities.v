(** Explicit index-equality charts for genuine linking-chain transport. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryAdjointUniqueness FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  CategoryAutomorphismConjugation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPCategoryAutomorphismConjugation.

Module DPLinkingChainTransportEqualities.

Lemma conjugate_iso_composition {C : category} {x y z : C}
    (e : isomorphism x y) (f : isomorphism y z) (a : hom C x x) :
  conjugate (isomorphism_composition e f) a = conjugate f (conjugate e a).
Proof.
unfold conjugate, isomorphism_composition; simpl.
rewrite !compose_assoc; reflexivity.
Qed.

Section Equalities.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.

Definition entry_equality_iso (i j : 'I_(length c).+1) (h : i = j) :
  @isomorphism (linking_category L) (entry c i) (entry c j) :=
  match h with Logic.eq_refl => @iso_refl (linking_category L) (entry c i) end.

Lemma projection_conjugate_equality (i j : 'I_(length c).+1) (h : i = j)
    (a : chain_automorphism_group L c) :
  conjugate (entry_equality_iso h) (@projection S F L c i a) = @projection S F L c j a.
Proof.
case: j / h; unfold conjugate, entry_equality_iso; simpl.
rewrite linking_id_left linking_id_right; reflexivity.
Qed.

Lemma inclusion_equality_square (i j i' j' : 'I_(length c).+1)
    (hi : i = i') (hj : j = j') (hij : i <= j) (hij' : i' <= j') :
  linking_compose L (@chain_inclusion S F L c i j hij) (iso_hom (entry_equality_iso hj)) =
    linking_compose L (iso_hom (entry_equality_iso hi)) (@chain_inclusion S F L c i' j' hij').
Proof.
case: i' / hi in hij' *; case: j' / hj in hij' *.
have -> : hij' = hij := Prop_irrelevance _ _.
change (linking_compose L (@chain_inclusion S F L c i j hij) (linking_identity L (entry c j)) =
  linking_compose L (linking_identity L (entry c i)) (@chain_inclusion S F L c i j hij)).
rewrite linking_id_left linking_id_right; reflexivity.
Qed.
End Equalities.
End DPLinkingChainTransportEqualities.
