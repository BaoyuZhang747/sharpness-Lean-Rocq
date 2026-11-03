(** The literal acting subgroup homomorphism into compatible chain
    automorphisms, with every transporter coordinate exposed. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainTransporter NormalizerChainEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChain
  DPNormalizerChainTransporter DPNormalizerChainEmbedding.
Local Open Scope group_scope.

Module DPLinkingChainActingHom.
Section Acting.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable P : {group S}.
Variable hP : P \subset normalizer c.

Definition acting_normalizer (x : [subg P]) : [subg (normalizer c)] :=
  Sub (val x) (subsetP hP _ (valP x)).

Definition acting_value (x : [subg P]) : chain_automorphism_group L c :=
  normalizer_embedding L (acting_normalizer x).

Lemma acting_value_mul (x y : [subg P]) : acting_value (x * y) = acting_value x * acting_value y.
Proof.
have h : acting_normalizer (x * y) = acting_normalizer x * acting_normalizer y.
  apply val_inj; reflexivity.
rewrite /acting_value h; exact: normalizer_embedding_mul.
Qed.

Definition acting_hom : {morphism [set: [subg P]] >-> chain_automorphism_group L c}.
Proof. apply: (Morphism (mfun := acting_value)); move=> x y _ _; exact: acting_value_mul. Defined.

Definition acting_coordinate (x : [subg P]) (i : 'I_(length c).+1) : [subg 'N(subgroup c i)] :=
  Sub (val x) (subsetP (subset_trans hP (@normalizer_sub S F c i)) _ (valP x)).

Theorem acting_hom_projection (x : [subg P]) (i : 'I_(length c).+1) :
  @projection S F L c i (acting_hom x) = normalizer_map L (acting_coordinate x i).
Proof.
change (@projection S F L c i (normalizer_embedding L (acting_normalizer x)) =
  normalizer_map L (acting_coordinate x i)).
rewrite normalizer_embedding_projection /coordinate.
congr (normalizer_map L _); apply val_inj; reflexivity.
Qed.

Theorem acting_hom_injective : injective acting_hom.
Proof.
move=> x y h; have hn := normalizer_embedding_injective h.
have hv := congr1 val hn; apply val_inj; exact hv.
Qed.
End Acting.
End DPLinkingChainActingHom.
