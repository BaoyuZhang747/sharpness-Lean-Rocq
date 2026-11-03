(** The actual finite group of compatible linking automorphism tuples.
    Compatibility is imposed at every pair of comparable chain entries. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite
  LinkingSystemCancellation LinkingSystemAutomorphisms LinkingChainObjects.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingFinite DPLinkingCancellation
  DPLinkingAutomorphisms DPLinkingChains.
Local Open Scope group_scope.

Module DPLinkingChainAutomorphisms.
Section Automorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation I := 'I_(length c).+1.

Definition chain_inclusion (i j : I) (hij : i <= j) :
    linking_hom L (entry c i) (entry c j) := inclusion L (entry_mono hij).

Lemma chain_inclusion_refl (i : I) : chain_inclusion (leqnn i) = linking_identity L (entry c i).
Proof.
have hp : entry_mono (leqnn i) = subxx (subgroup c i) := Prop_irrelevance _ _.
rewrite /chain_inclusion hp; exact: inclusion_identity.
Qed.

Lemma chain_inclusion_compose (i j k : I) (hij : i <= j) (hjk : j <= k) :
  linking_compose L (chain_inclusion hij) (chain_inclusion hjk) =
    chain_inclusion (leq_trans hij hjk).
Proof.
rewrite /chain_inclusion.
transitivity (inclusion L (subset_trans (entry_mono hij) (entry_mono hjk))).
- exact: inclusion_compose.
- congr (inclusion L _); exact: Prop_irrelevance.
Qed.

Definition tuple_type : finType :=
  [the finType of {dffun forall i : I, automorphism_group L (entry c i)}].

Definition tuple_mul (a b : tuple_type) : tuple_type := [ffun i => a i * b i].
Definition tuple_one : tuple_type := [ffun i => 1].
Definition tuple_inv (a : tuple_type) : tuple_type := [ffun i => (a i)^-1].

Lemma tuple_mul_assoc : associative tuple_mul.
Proof. move=> a b d; apply/ffunP=> i; by rewrite /tuple_mul !ffunE mulgA. Qed.
Lemma tuple_one_left : left_id tuple_one tuple_mul.
Proof. move=> a; apply/ffunP=> i; by rewrite /tuple_mul /tuple_one !ffunE mul1g. Qed.
Lemma tuple_inv_left : left_inverse tuple_one tuple_inv tuple_mul.
Proof. move=> a; apply/ffunP=> i; by rewrite /tuple_mul /tuple_inv /tuple_one !ffunE mulVg. Qed.

Definition tuple_group : finGroupType :=
  HB.pack tuple_type (Finite_isGroup.Build tuple_type tuple_mul_assoc tuple_one_left tuple_inv_left).

Lemma tuple_mulE (a b : tuple_group) (i : I) : (a * b) i = a i * b i.
Proof. change (tuple_mul a b i = a i * b i); by rewrite /tuple_mul ffunE. Qed.
Lemma tuple_oneE (i : I) : (1 : tuple_group) i = 1.
Proof. change (tuple_one i = 1); by rewrite /tuple_one ffunE. Qed.
Lemma tuple_invE (a : tuple_group) (i : I) : a^-1 i = (a i)^-1.
Proof. change (tuple_inv a i = (a i)^-1); by rewrite /tuple_inv ffunE. Qed.

Definition comparable_indices := {ij : I * I | ij.1 <= ij.2}.

Definition compatible_square (a : tuple_group) (ij : comparable_indices) : bool :=
  (linking_compose L (a (val ij).1) (chain_inclusion (valP ij)) :
     hom_finType L (entry c (val ij).1) (entry c (val ij).2)) ==
    linking_compose L (chain_inclusion (valP ij)) (a (val ij).2).

Definition compatible (a : tuple_group) : bool := [forall ij, compatible_square a ij].

Lemma compatibleP (a : tuple_group) : reflect
  (forall (i j : I) (hij : i <= j),
    linking_compose L (a i) (chain_inclusion hij) =
      linking_compose L (chain_inclusion hij) (a j)) (compatible a).
Proof.
apply: (iffP forallP).
- move=> h i j hij; have hs := h (exist (fun ij : I * I => is_true (ij.1 <= ij.2)) (i,j) hij).
  have hs' := elimT eqP hs.
  have hp : valP (exist (fun ij : I * I => is_true (ij.1 <= ij.2)) (i,j) hij) = hij :=
    Prop_irrelevance _ _.
  by rewrite hp in hs'.
- move=> h [ij hij]; rewrite /compatible_square; apply/eqP; exact: h.
Qed.

Lemma compatible_one : compatible (1 : tuple_group).
Proof.
apply/compatibleP=> i j hij; rewrite !tuple_oneE.
change (linking_compose L (linking_identity L (entry c i)) (chain_inclusion hij) =
  linking_compose L (chain_inclusion hij) (linking_identity L (entry c j))).
by rewrite linking_id_left linking_id_right.
Qed.

Lemma compatible_mul (a b : tuple_group) : compatible a -> compatible b -> compatible (a * b).
Proof.
move/compatibleP=> ha /compatibleP hb; apply/compatibleP=> i j hij.
rewrite !tuple_mulE !automorphism_mul.
by rewrite linking_assoc (hb i j hij) -linking_assoc (ha i j hij) linking_assoc.
Qed.

Definition compatible_set : {set tuple_group} := [set a | compatible a].
Lemma compatible_group_set : group_set compatible_set.
Proof.
apply/group_setP; split.
- rewrite inE; exact: compatible_one.
- move=> a b; rewrite !inE; exact: compatible_mul.
Qed.

Definition compatible_group : {group tuple_group} := Group compatible_group_set.
Definition chain_automorphism_group : finGroupType := [the finGroupType of [subg compatible_group]%type].

Definition projection (i : I) (a : chain_automorphism_group) :
    automorphism_group L (entry c i) := (val a) i.

Lemma projection_morphic (i : I) : morphic [set: chain_automorphism_group] (projection i).
Proof. apply/morphicP=> a b _ _; exact: tuple_mulE. Qed.

Definition projection_morphism (i : I) :
    {morphism [set: chain_automorphism_group] >-> automorphism_group L (entry c i)} :=
  [morphism of morphm (projection_morphic i)].

Lemma projection_square (a : chain_automorphism_group) (i j : I) (hij : i <= j) :
  linking_compose L (projection i a) (chain_inclusion hij) =
    linking_compose L (chain_inclusion hij) (projection j a).
Proof.
have ha := valP a; rewrite inE in ha; move/compatibleP: ha=> ha.
exact: ha.
Qed.

Lemma projection_ext (a b : chain_automorphism_group) :
  (forall i, projection i a = projection i b) -> a = b.
Proof. move=> hab; apply val_inj; apply/ffunP; exact: hab. Qed.

Theorem top_projection_injective : injective (projection ord_max).
Proof.
move=> a b he; apply: projection_ext=> i.
apply (@compose_right_injective S F L (entry c i) (entry c i) (entry c ord_max)
  (@chain_inclusion i ord_max (leq_ord i))).
by rewrite !projection_square he.
Qed.

End Automorphisms.
End DPLinkingChainAutomorphisms.

Check DPLinkingChainAutomorphisms.chain_automorphism_group.
Print Assumptions DPLinkingChainAutomorphisms.compatible_group_set.
Print Assumptions DPLinkingChainAutomorphisms.top_projection_injective.


