(** A genuine terminal singleton in the isomorphism-pointed evaluation comma. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryLimits CategoryComma CategoryAdjointUniqueness
  FusionSystems FusionOrbit.
From DiazParkV16b Require Import CategoryAutomorphismConjugation LinkingSystem LinkingChainObjects
  LinkingChainAutomorphisms NormalizerChainIndices LinkingChainRestrictionMaps
  LinkingChainRestrictionUniqueness LinkingChainTransportEqualities NormalizerLinkingChainExt
  NormalizerLinkingChainComponents NormalizerLinkingChainCategory NormalizerLinkingChainEvaluation
  NormalizerLinkingEvaluationPrefix NormalizerLinkingEvaluationPoints.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryAutomorphismConjugation DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndices DPLinkingChainRestrictionMaps DPLinkingChainRestrictionUniqueness
  DPLinkingChainTransportEqualities DPNormalizerLinkingChainExt DPNormalizerLinkingChainComponents
  DPNormalizerLinkingChainCategory DPNormalizerLinkingChainEvaluation
  DPNormalizerLinkingEvaluationPrefix DPNormalizerLinkingEvaluationPoints.

Module DPNormalizerLinkingEvaluationTerminal.
Section Terminal.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.

Definition terminal_point : evaluation_point L P :=
  @Build_evaluation_point S F L P (singleton P)
    (object_equality_iso L (esym (@singleton_entry S F P ord0))).

Definition terminal_selector (x : evaluation_point L P) : selector (point_chain x) (singleton P).
Proof.
apply: (Sub [ffun _ : 'I_1 => (ord0 : 'I_(length (point_chain x)).+1)]).
apply/increasingP=> i j hij.
by rewrite (ord1 i) (ord1 j) ltnn in hij.
Defined.

Lemma terminal_selector_index (x : evaluation_point L P) i : index (terminal_selector x) i = ord0.
Proof. exact: ffunE. Qed.

Definition terminal_entry_iso (x : evaluation_point L P) i :
  @isomorphism (linking_category L)
    (entry (point_chain x) (index (terminal_selector x) i)) (entry (singleton P) i) :=
  isomorphism_composition (entry_equality_iso L (terminal_selector_index x i))
    (isomorphism_composition (iso_symm (point_iso x))
      (object_equality_iso L (esym (@singleton_entry S F P i)))).

Lemma terminal_entry_square (x : evaluation_point L P)
    (i j : 'I_(length (singleton P)).+1) (hij : i <= j) :
  linking_compose L
    (@chain_inclusion S F L (point_chain x) _ _ (index_mono (terminal_selector x) hij))
    (iso_hom (terminal_entry_iso x j)) =
  linking_compose L (iso_hom (terminal_entry_iso x i)) (@chain_inclusion S F L (singleton P) i j hij).
Proof.
have hi : i = ord0 := ord1 i; subst i.
have hj : j = ord0 := ord1 j; subst j.
have hs : index_mono (terminal_selector x) hij = leqnn (index (terminal_selector x) ord0) :=
  Prop_irrelevance _ _.
have ht : hij = leqnn (ord0 : 'I_1) := Prop_irrelevance _ _.
by rewrite hs ht !chain_inclusion_refl linking_id_left linking_id_right.
Qed.

Definition terminal_chain_map (x : evaluation_point L P) : chain_map L (point_chain x) (singleton P) :=
  @Build_chain_map S F L (point_chain x) (singleton P) (terminal_selector x)
    (terminal_entry_iso x) (terminal_entry_square x).

Lemma terminal_chain_map_evaluation (x : evaluation_point L P) :
  evaluation_arrow (terminal_chain_map x) =
  linking_compose L (iso_inv (point_iso x)) (iso_hom (point_iso terminal_point)).
Proof.
change (linking_compose L (@bottom_inclusion S F L (point_chain x) (index (terminal_selector x) ord0))
  (linking_compose L (iso_hom (entry_equality_iso L (terminal_selector_index x ord0)))
    (linking_compose L (iso_inv (point_iso x))
      (iso_hom (object_equality_iso L (esym (@singleton_entry S F P ord0)))))) =
  linking_compose L (iso_inv (point_iso x)) (iso_hom (point_iso terminal_point))).
rewrite -linking_assoc bottom_inclusion_chart bottom_inclusion_refl linking_id_left; reflexivity.
Qed.

Definition terminal_arrow (x : evaluation_points L P) : hom (evaluation_points L P) x terminal_point.
Proof.
refine (@Build_costructured_hom (opposite (chain_category L)) (opposite (linking_category L))
  (functor_op (evaluation L)) P (point_under terminal_point) (point_under x) (terminal_chain_map x) _).
change (linking_compose L (iso_hom (point_iso x)) (evaluation_arrow (terminal_chain_map x)) =
  iso_hom (point_iso terminal_point)).
rewrite terminal_chain_map_evaluation -linking_assoc.
have he := iso_hom_inv (point_iso x).
change (linking_compose L (iso_hom (point_iso x)) (iso_inv (point_iso x)) =
  linking_identity L P) in he.
by rewrite he linking_id_left.
Defined.

Lemma bottom_inclusion_eq_chart (c : chain F) (i : 'I_(length c).+1) (h : i = ord0) :
  @bottom_inclusion S F L c i = iso_hom (@entry_equality_iso S F L c ord0 i (esym h)).
Proof. subst i; rewrite bottom_inclusion_refl entry_chart_loop; reflexivity. Qed.

Lemma entry_at_bottom (c d : chain F) (f : chain_map L c d)
    (i : 'I_(length d).+1) (h : index (selected_indices f) i = ord0) :
  @entry_at S F L c d f i ord0 h = bottom_arrow f i.
Proof. rewrite /entry_at /bottom_arrow (bottom_inclusion_eq_chart h); reflexivity. Qed.

Lemma terminal_arrow_unique (x : evaluation_points L P) (f : hom (evaluation_points L P) x terminal_point) :
  f = terminal_arrow x.
Proof.
apply costructured_hom_ext.
change (point_map f = terminal_chain_map x).
have heval : evaluation_arrow (point_map f) = evaluation_arrow (terminal_chain_map x).
  apply (@iso_cancel_left (linking_category L) P (entry (point_chain x) ord0)
    (entry (singleton P) ord0) (point_iso x)).
  change (linking_compose L (iso_hom (point_iso x)) (evaluation_arrow (point_map f)) =
    linking_compose L (iso_hom (point_iso x)) (evaluation_arrow (terminal_chain_map x))).
  exact (eq_trans (point_map_square f) (esym (point_map_square (terminal_arrow x)))).
have he := selected_indices_unique (point_map f) (terminal_chain_map x).
have hf i : index (selected_indices (point_map f)) i = ord0.
  rewrite he; exact: terminal_selector_index.
apply (@chain_map_ext_at S F L (point_chain x) (singleton P) (point_map f) (terminal_chain_map x)
  (fun _ => ord0) hf (terminal_selector_index x))=> i.
rewrite !entry_at_bottom (ord1 i); exact heval.
Qed.

Definition points_terminal : terminal_object (evaluation_points L P) :=
  @Build_terminal_object (evaluation_points L P) terminal_point terminal_arrow terminal_arrow_unique.

End Terminal.
End DPNormalizerLinkingEvaluationTerminal.
