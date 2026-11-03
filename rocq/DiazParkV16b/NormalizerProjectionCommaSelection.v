(** The selected indices of actual extensions to a fixed target chain are
    forced by subgroup orders. Restriction to that selected chain is literal. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensions.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaSelection.
Section Selection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.

Lemma entry_card_injective : injective (fun i => #|subgroup c i|).
Proof.
move=> i j he; case: (ltngtP (val i) (val j))=> hij.
- have h := proper_card (@entry_strict S F c i j hij); by rewrite he ltnn in h.
- have h := proper_card (@entry_strict S F c j i hij); by rewrite he ltnn in h.
- exact: val_inj hij.
Qed.

Lemma extension_entry_card (P Q : {group S}) (f : DPFusion.map P Q)
    (a : extension c d f) i : #|subgroup c (index (indices a) i)| = #|subgroup d i|.
Proof.
rewrite -(entry_images a i) card_injm ?map_injm ?entry_sub_carrier //.
Qed.

Theorem indices_unique (P Q U V : {group S}) (f : DPFusion.map P Q) (g : DPFusion.map U V)
    (a : extension c d f) (b : extension c d g) : indices a = indices b.
Proof.
apply val_inj; apply/ffunP=> i; apply: entry_card_injective.
by rewrite (extension_entry_card a i) (extension_entry_card b i).
Qed.

Definition on_selected (P Q : {group S}) (f : DPFusion.map P Q)
    (a : extension c d f) : extension (selected_chain (indices a)) d f.
Proof.
refine (@Build_extension S F (selected_chain (indices a)) d P Q f
  (DPNormalizerChainIndices.identity d) (carrier a) (acting_sub a) _
  (extension_map a) (extension_allowed a) (on_acting a) _).
- rewrite identity_index /subgroup selected_chain_entry; exact: chain_sub a.
- move=> i; rewrite identity_index /subgroup selected_chain_entry; exact: entry_images a i.
Defined.
End Selection.
End DPNormalizerProjectionCommaSelection.
