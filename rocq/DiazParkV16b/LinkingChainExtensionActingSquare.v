(** Exact normalizer-action compatibility for a full-carrier linking lift. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemCancellation
  LinkingSystemAutomorphisms LinkingSystemNormalizerSquares
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainIndices
  NormalizerChainExtensions NormalizerChainNormalizer NormalizerChainTransporter
  CategoryAutomorphismConjugation LinkingChainRestrictionMaps LinkingChainActingHom
  LinkingChainExtensionActingLift.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingCancellation DPLinkingAutomorphisms
  DPLinkingNormalizerSquares DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPNormalizerChainExtensions DPNormalizerChain
  DPNormalizerChainTransporter DPCategoryAutomorphismConjugation
  DPLinkingChainRestrictionMaps DPLinkingChainActingHom DPLinkingChainExtensionActingLift.
Local Open Scope group_scope.

Module DPLinkingChainExtensionActingSquare.
Section Square.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables c d : chain F.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension c d f.
Hypothesis cP : DPFusionSystem.centric F P.
Hypothesis hP : P \subset normalizer c.
Hypothesis hQ : Q \subset normalizer d.
Local Notation e := (indices a).
Local Notation V := (carrier_object a cP).
Local Notation T := (ambient_object cP).
Local Notation b := (carrier_lift L a cP).
Local Notation Phi := (extension_chain_map L a cP).

Definition image_element (x : [subg P]) : [subg Q] := Sub (f (val x)) (map_into f (valP x)).

Lemma image_element_value (x : [subg P]) : val (image_element x) = f (val x).
Proof. reflexivity. Qed.

Definition carrier_element (x : [subg P]) : [subg (val V)] :=
  Sub (val x) (subsetP (acting_sub a) _ (valP x)).

Definition ambient_element (x : [subg P]) : [subg (val T)] :=
  arrow_element (linking_projection L b) (carrier_element x).

Lemma ambient_element_value (x : [subg P]) : val (ambient_element x) = f (val x).
Proof.
change (val (linking_projection L b) (val x) = f (val x)).
rewrite carrier_lift_projection; exact: on_acting (valP x).
Qed.

Definition source_inclusion (i : 'I_(length d).+1) :=
  @DPCentricLinking.inclusion S F L (entry c (index e i)) V (entry_sub_carrier a i).

Definition target_inclusion (i : 'I_(length d).+1) :=
  @DPCentricLinking.inclusion S F L (entry d i) T (subsetT (subgroup d i)).

Lemma source_action_square (x : [subg P]) (i : 'I_(length d).+1) :
  linking_compose L (normalizer_map L (acting_coordinate hP x (index e i))) (source_inclusion i) =
  linking_compose L (source_inclusion i) (distinguished L (carrier_element x)).
Proof.
have hh := @normalizer_inclusion_square S F L (entry c (index e i)) V (entry_sub_carrier a i)
  (carrier_element x) (valP (acting_coordinate hP x (index e i))).
have he : Sub (val (carrier_element x)) (valP (acting_coordinate hP x (index e i))) =
  acting_coordinate hP x (index e i).
  apply val_inj; reflexivity.
by rewrite he in hh.
Qed.

Lemma ambient_element_normalizes (x : [subg P]) (i : 'I_(length d).+1) :
  val (ambient_element x) \in 'N(subgroup d i).
Proof.
rewrite ambient_element_value.
exact (valP (acting_coordinate hQ (image_element x) i)).
Qed.

Lemma target_action_square (x : [subg P]) (i : 'I_(length d).+1) :
  linking_compose L (normalizer_map L (acting_coordinate hQ (image_element x) i)) (target_inclusion i) =
  linking_compose L (target_inclusion i) (distinguished L (ambient_element x)).
Proof.
have hh := @normalizer_inclusion_square S F L (entry d i) T (subsetT (subgroup d i))
  (ambient_element x) (ambient_element_normalizes x i).
have he : Sub (val (ambient_element x)) (ambient_element_normalizes x i) =
  acting_coordinate hQ (image_element x) i.
  apply val_inj; exact: ambient_element_value.
by rewrite he in hh.
Qed.

Lemma entry_action_intertwines (x : [subg P]) (i : 'I_(length d).+1) :
  linking_compose L (normalizer_map L (acting_coordinate hP x (index e i)))
    (iso_hom (entry_isomorphism Phi i)) =
  linking_compose L (iso_hom (entry_isomorphism Phi i))
    (normalizer_map L (acting_coordinate hQ (image_element x) i)).
Proof.
apply (@compose_right_injective S F L (entry c (index e i)) (entry d i) T (target_inclusion i)).
change (linking_compose L
  (linking_compose L (normalizer_map L (acting_coordinate hP x (index e i))) (entry_lift L a cP i))
  (target_inclusion i) =
  linking_compose L (linking_compose L (entry_lift L a cP i)
    (normalizer_map L (acting_coordinate hQ (image_element x) i))) (target_inclusion i)).
rewrite !linking_assoc target_action_square.
change (linking_compose L (normalizer_map L (acting_coordinate hP x (index e i)))
  (linking_compose L (entry_lift L a cP i) (target_inclusion i)) =
  linking_compose L (entry_lift L a cP i)
    (linking_compose L (target_inclusion i) (distinguished L (ambient_element x)))).
rewrite -[RHS]linking_assoc.
have hs : linking_compose L (entry_lift L a cP i) (target_inclusion i) =
  linking_compose L (source_inclusion i) b := entry_lift_square L a cP i.
rewrite !hs -[LHS]linking_assoc source_action_square !linking_assoc.
congr (linking_compose L (source_inclusion i) _).
exact (@commutation S F L V T b (carrier_element x)).
Qed.

Theorem extension_acting_square (x : [subg P]) :
  restriction_morphism Phi (acting_hom L hP x) = acting_hom L hQ (image_element x).
Proof.
apply projection_ext=> i.
rewrite restriction_morphism_component !acting_hom_projection.
change (@conjugate (linking_category L) _ _ (entry_isomorphism Phi i)
  (normalizer_map L (acting_coordinate hP x (index e i))) =
  normalizer_map L (acting_coordinate hQ (image_element x) i)).
apply (@iso_cancel_left (linking_category L) _ _ _ (entry_isomorphism Phi i)).
rewrite conjugate_intertwines.
exact: entry_action_intertwines.
Qed.
End Square.
End DPLinkingChainExtensionActingSquare.
