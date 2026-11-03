(** The actual chain-to-conjugate-subchain relation given by simultaneous
    extensions with trivial acting subgroup. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensions.
Local Open Scope group_scope.

Module DPNormalizerChainRelations.
Section Relations.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition forget_acting (c d : chain F) (P Q : {group S}) (f : DPFusion.map P Q)
    (a : extension c d f) : extension c d (DPFusion.identity 1%G).
Proof.
refine (@Build_extension S F c d 1%G 1%G (DPFusion.identity 1%G)
  (indices a) (carrier a) (sub1G _) (chain_sub a)
  (extension_map a) (extension_allowed a) _ (entry_images a)).
move=> x /set1P ->; by rewrite !map_one.
Defined.

Definition chain_witness (c d : chain F) := extension c d (DPFusion.identity 1%G).
Definition subconjugate (c d : chain F) := asbool (inhabited (chain_witness c d)).

Lemma subconjugateP (c d : chain F) : reflect (inhabited (chain_witness c d)) (subconjugate c d).
Proof. exact: asboolP. Qed.

Lemma subconjugate_refl : reflexive subconjugate.
Proof. move=> c; apply/subconjugateP; exact (inhabits (identity_extension 1%G c)). Qed.

Lemma subconjugate_trans : transitive subconjugate.
Proof.
move=> c d t /subconjugateP[a] /subconjugateP[b].
apply/subconjugateP.
have h := compose_extension a b.
rewrite identity_compose in h; exact (inhabits h).
Qed.

Lemma extension_subconjugate (c d : chain F) (P Q : {group S}) (f : DPFusion.map P Q)
    (a : extension c d f) : subconjugate c d.
Proof. apply/subconjugateP; exact (inhabits (forget_acting a)). Qed.

Lemma subconjugate_length (c d : chain F) : subconjugate c d -> length d <= length c.
Proof. move/subconjugateP=> [a]; exact: selector_length (indices a). Qed.

Definition mutually_subconjugate (c d : chain F) := subconjugate c d && subconjugate d c.

Lemma mutually_subconjugate_refl : reflexive mutually_subconjugate.
Proof. move=> c; by rewrite /mutually_subconjugate subconjugate_refl. Qed.

Lemma mutually_subconjugate_sym : symmetric mutually_subconjugate.
Proof. move=> c d; exact: andbC. Qed.

Lemma mutually_subconjugate_trans : transitive mutually_subconjugate.
Proof.
move=> c d t /andP[hcd hdc] /andP[hdt htd]; apply/andP; split.
- exact: subconjugate_trans hcd hdt.
- exact: subconjugate_trans htd hdc.
Qed.

Lemma mutually_subconjugate_length (c d : chain F) :
  mutually_subconjugate c d -> length c = length d.
Proof.
move/andP=> [hcd hdc]; apply/eqP; rewrite eqn_leq; apply/andP; split;
  exact: subconjugate_length.
Qed.

Lemma subconjugate_congr (c c' d d' : chain F) :
  mutually_subconjugate c c' -> mutually_subconjugate d d' ->
  subconjugate c d = subconjugate c' d'.
Proof.
move/andP=> [hcc hcc']; move/andP=> [hdd hdd']; apply/idP/idP=> h.
- exact: subconjugate_trans hcc' (subconjugate_trans h hdd).
- exact: subconjugate_trans hcc (subconjugate_trans h hdd').
Qed.

End Relations.
End DPNormalizerChainRelations.
