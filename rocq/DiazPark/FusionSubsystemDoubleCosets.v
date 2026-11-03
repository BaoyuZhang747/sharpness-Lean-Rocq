From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionCentralizerMaps FusionMackeyShape
  TraceNormalizerCosets FusionSubsystemRestriction.
Import DPFusionSubgroup DPFusionMackey DPFusionSubsystemRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPSubsystemDoubleCosets.
Section Embedding.
Variable S : finGroupType.
Variable C : {group S}.
Local Notation U := [subg C]%type.

Lemma ambient_set (P : {group U}) : val @: P = ambient P.
Proof. change (val @: P = sgval @* P). by rewrite morphimE setTI. Qed.

Lemma ambient_apex (P Q : {group U}) (t : U) :
    ambient (inclusion_apex P Q t) = inclusion_apex (ambient P) (ambient Q) (val t).
Proof.
apply val_inj; rewrite /ambient /inclusion_apex /=.
by rewrite (injmI (injm_sgval C)) morphimJ ?inE.
Qed.

Lemma ambient_double_coset (P Q : {group U}) (t : U) :
    val @: double_coset P Q t = double_coset (ambient P) (ambient Q) (val t).
Proof.
apply/setP=> x; apply/imsetP/double_cosetP.
- move=> [y /double_cosetP[a [b [ha [hb ->]]]] ->].
  exists (val a), (val b); split; first exact: ambient_mem ha.
  split; first exact: ambient_mem hb.
  reflexivity.
- move=> [a [b [ha [hb ->]]]].
  exists (subg C a*t*subg C b).
  + apply/double_cosetP; exists (subg C a), (subg C b).
    by repeat split; try exact: ambient_repr.
  + change (a*val t*b = val (subg C a)*val t*val (subg C b)).
    by rewrite (ambient_subgK ha) (ambient_subgK hb).
Qed.

Variables P Q T : {group U}.

Lemma ambient_index_mem (i : double_coset_index P Q T) :
    val @: val i \in double_coset (ambient P) (ambient Q) @: ambient T.
Proof.
apply/imsetP; exists (val (double_coset_representative i)).
- exact: ambient_mem (double_coset_representative_mem i).
- by rewrite -ambient_double_coset double_coset_representative_set.
Qed.

Definition ambient_index (i : double_coset_index P Q T) :
    double_coset_index (ambient P) (ambient Q) (ambient T) :=
  Sub (val @: val i) (ambient_index_mem i).

Lemma ambient_index_injective : injective ambient_index.
Proof.
move=> i j he; apply: val_inj.
have hh := congr1 (fun z : double_coset_index (ambient P) (ambient Q) (ambient T) => val z) he.
change (val @: val i = val @: val j) in hh.
exact: (imset_inj (@val_inj _ _ _) hh).
Qed.

Lemma ambient_index_surjective j : exists i, ambient_index i = j.
Proof.
pose t := double_coset_representative j.
have ht : t \in ambient T := double_coset_representative_mem j.
have hl : double_coset P Q (subg C t) \in double_coset P Q @: T.
  apply/imsetP; exists (subg C t); [exact: ambient_repr ht | reflexivity].
pose i : double_coset_index P Q T := Sub (double_coset P Q (subg C t)) hl.
exists i; apply: val_inj.
change (val @: double_coset P Q (subg C t) = val j).
rewrite ambient_double_coset (ambient_subgK ht).
exact: double_coset_representative_set.
Qed.

Lemma ambient_index_inverse_exists j : exists i, ambient_index i == j.
Proof. by have [i he] := ambient_index_surjective j; exists i; rewrite he. Qed.

Definition local_index j := xchoose (ambient_index_inverse_exists j).

Lemma ambient_index_local j : ambient_index (local_index j) = j.
Proof. exact: eqP (xchooseP (ambient_index_inverse_exists j)). Qed.

Lemma local_index_ambient i : local_index (ambient_index i) = i.
Proof. apply: ambient_index_injective; exact: ambient_index_local. Qed.

Lemma ambient_index_bijective : bijective ambient_index.
Proof. exists local_index; [exact: local_index_ambient | exact: ambient_index_local]. Qed.

Lemma ambient_representative i :
    double_coset (ambient P) (ambient Q) (double_coset_representative (ambient_index i)) =
    double_coset (ambient P) (ambient Q) (val (double_coset_representative i)).
Proof.
rewrite double_coset_representative_set /= -ambient_double_coset.
by rewrite double_coset_representative_set.
Qed.
End Embedding.
End DPSubsystemDoubleCosets.

Print Assumptions DPSubsystemDoubleCosets.ambient_index_bijective.





