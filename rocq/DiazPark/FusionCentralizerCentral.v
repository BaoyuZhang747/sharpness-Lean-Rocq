From mathcomp Require Import all_ssreflect all_fingroup center.
From DiazPark Require Import FusionMaps FusionSystems FusionCentralizerMaps FusionCentralizer FusionQuotientMaps.
Import DPFusion DPFusionSubgroup DPFusionCentralizer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerCentral.
Section Central.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Hypothesis abE : abelian E.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.

Definition embedded : {group T} := (subg C @* E)%G.

Lemma embedded_ambient : ambient embedded = E.
Proof. apply: val_inj; change (sgval @* (subg C @* E) = E); exact: subgmK abE. Qed.

Lemma embedded_join (P : {group T}) : ambient (P <*> embedded)%G = joint (E := E) P.
Proof. by rewrite ambient_join embedded_ambient. Qed.

Lemma joint_embedded_join (P : {group T}) :
  joint (E := E) (P <*> embedded)%G = joint (E := E) P.
Proof.
apply: val_inj; change (ambient (P <*> embedded)%G <*> E = ambient P <*> E).
have eEE : E <*> E = E by apply/joing_idPl.
by rewrite embedded_join /joint /= -joingA eEE.
Qed.

Lemma embedded_sub_center : embedded \subset 'Z([set: T]).
Proof.
apply/subsetP=> e Ee; apply/setIP; split; first by rewrite inE.
apply/centP=> x _; apply: val_inj.
have Ev := ambient_mem Ee.
rewrite embedded_ambient in Ev.
change (val e * val x = val x * val e).
exact: esym (centP (valP x) (val e) Ev).
Qed.

Theorem embedded_central : DPFusionQuotient.central (system F E) embedded.
Proof.
constructor; first exact: embedded_sub_center.
move=> P Q f /allowedP[fhat [hf [hext hfix]]].
pose g0 := reindex (esym (embedded_join P)) (esym (embedded_join Q)) fhat.
pose g := lower g0.
have hg : DPFusionSystem.allowed (system F E) g.
  apply/allowedP.
  exists (reindex (esym (joint_embedded_join P)) (esym (joint_embedded_join Q)) fhat).
  split; first exact: reindex_allowed hf.
  split.
  - move=> x Px; rewrite reindexE /g lowerE // /g0 reindexE.
    by [].
  - by move=> e Ee; rewrite reindexE hfix.
exists g; split=> //; split.
- move=> x Px; apply: val_inj.
  rewrite /g lowerE ?(subsetP (joing_subl P embedded) x Px) // /g0 reindexE.
  exact: hext x Px.
- move=> e Ee; apply: val_inj.
  rewrite /g lowerE ?(subsetP (joing_subr P embedded) e Ee) // /g0 reindexE.
  apply: hfix; have h := ambient_mem Ee.
  by rewrite embedded_ambient in h.
Qed.
End Central.
End DPFusionCentralizerCentral.
