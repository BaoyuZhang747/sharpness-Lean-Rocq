(** Actual image chains under fusion injections of the top subgroup.
    Strictness and centricity are proved, with no chosen length bound. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionCentricBasics.
From DiazParkV16b Require Import LinkingChainObjects.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPFusion.
Local Open Scope group_scope.

Module DPNormalizerChainTransport.
Section Transport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable Q : {group S}.
Variable f : DPFusion.map (val (top c)) Q.
Hypothesis hf : DPFusionSystem.allowed F f.
Local Notation I := 'I_(length c).+1.

Definition entry_map (i : I) := DPFusion.restrict f (@entry_sub_top S F c i).
Definition entry_image (i : I) := DPFusion.image (entry_map i).

Lemma entry_image_morphism i :
  entry_image i = (DPFusion.map_morphism f @* subgroup c i)%G.
Proof.
apply val_inj.
change (DPFusion.map_morphism (DPFusion.restrict f (@entry_sub_top S F c i)) @*
  subgroup c i = DPFusion.map_morphism f @* subgroup c i).
by rewrite /DPFusion.restrict DPFusion.of_morphism_image im_restrm.
Qed.

Lemma entry_image_centric i : DPFusionSystem.centric F (entry_image i).
Proof.
apply: DPFusionCentricBasics.centric_image (valP (entry c i)).
exact: DPFusionSystem.restriction_allowed hf.
Qed.

Definition transported_entry (i : I) : DPFusionOrbit.centric_object F :=
  Sub (entry_image i) (entry_image_centric i).
Definition transported_entries := [ffun i : I => transported_entry i].

Lemma transported_strict : strict_entries transported_entries.
Proof.
apply/strict_entriesP=> i j hij.
rewrite /transported_entries !ffunE.
change (is_true (entry_image i \proper entry_image j)).
rewrite !entry_image_morphism.
rewrite properEcard (morphimS (DPFusion.map_morphism f)
  (@entry_mono S F c i j (ltnW hij))) /=.
rewrite !card_injm ?DPFusion.map_injm ?entry_sub_top //.
exact: proper_card (@entry_strict S F c i j hij).
Qed.

Definition transport : chain F := of_entries transported_strict.

Lemma transport_length : length transport = length c.
Proof. reflexivity. Qed.

Lemma transport_entry i : entry transport i = transported_entry i.
Proof. exact: ffunE. Qed.

Lemma transport_subgroup i :
  subgroup transport i = (DPFusion.map_morphism f @* subgroup c i)%G.
Proof. rewrite /subgroup transport_entry; exact: entry_image_morphism. Qed.

Lemma transport_mem i x (hx : x \in val (top c)) :
  (f x \in subgroup transport i) = (x \in subgroup c i).
Proof.
rewrite transport_subgroup; apply/idP/idP.
- move/morphimP=> [y hy hiy hxy].
  have hi := elimT injmP (DPFusion.map_injm f).
  have -> : x = y := hi x y hx hy hxy.
  exact hiy.
- move=> hi; exact: mem_morphim hx hi.
Qed.

Lemma transport_top_image : val (top transport) = DPFusion.image f.
Proof. exact: transport_subgroup. Qed.

Lemma transport_top (honto : DPFusion.image f = Q) : val (top transport) = Q.
Proof. by rewrite transport_top_image. Qed.

End Transport.
End DPNormalizerChainTransport.
