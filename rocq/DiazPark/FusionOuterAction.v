From mathcomp Require Import all_ssreflect all_fingroup quotient generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionAutomorphisms FusionOrbit FusionOuterAutomorphisms FusionOuterOrbit.
Import DPFusion DPFusionAutomorphisms DPFusionOrbit DPFusionOuter DPFusionOuterOrbit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionOuterAction.
Section Action.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : {group S}.
Local Notation A := (DPFusionSaturation.aut_group F P).
Local Notation G := (outer_group F P).

Definition representative (g : coset_of (inner P)) : {perm S} :=
  odflt 1 [pick a : {perm S} | (a \in A) && (coset (inner P) a == g)].

Lemma representative_spec g : g \in G ->
  (representative g \in A) /\ coset (inner P) (representative g) = g.
Proof.
move=> /morphimP[a _ Aa ->].
rewrite /representative; case: pickP=> [b /andP[Ab /eqP eb] | hn].
- by split.
- have h := hn a; by rewrite Aa eqxx in h.
Qed.

Lemma representative_allowed g : g \in G -> representative g \in A.
Proof. by move=> /representative_spec[]. Qed.
Lemma representative_coset g : g \in G -> coset (inner P) (representative g) = g.
Proof. by move=> /representative_spec[]. Qed.

Definition outer_orbit g := aut_orbit F P (representative g).

Lemma outer_orbit_coset a : a \in A -> outer_orbit (coset (inner P) a) = aut_orbit F P a.
Proof.
move=> Aa.
have Ga : coset (inner P) a \in G := mem_quotient (inner P) Aa.
have [Ar er] := representative_spec Ga.
exact: (proj2 (aut_orbit_coset_eq Ar Aa) er).
Qed.

Lemma outer_orbit_one : outer_orbit 1 = orbit_identity F P.
Proof.
have h := outer_orbit_coset (group1 A).
rewrite morph1 in h; by rewrite h aut_orbit_one.
Qed.

Lemma outer_orbit_mul g h : g \in G -> h \in G ->
  outer_orbit (g*h) = orbit_compose (outer_orbit g) (outer_orbit h).
Proof.
move=> Gg Gh.
have [Ag eg] := representative_spec Gg.
have [Ah eh] := representative_spec Gh.
have Ng := subsetP (normal_norm (inner_normal F P)) _ Ag.
have Nh := subsetP (normal_norm (inner_normal F P)) _ Ah.
have egh : coset (inner P) (representative g * representative h) = g*h.
  rewrite (morphM (coset (inner P)) Ng Nh).
  exact: (congr2 (fun x y : coset_of (inner P) => x*y) eg eh).
rewrite -egh (outer_orbit_coset (groupM Ag Ah)) aut_orbit_mul //.
Qed.

(** Forward precomposition is a left action for MathComp's right-composition
    multiplication. Passing to inverse group elements gives the equivalent
    usual-function-composition convention of the manuscript. *)
Definition action (Q : {group S}) (g : coset_of (inner P)) (f : orbit_hom F P Q) :=
  orbit_compose (outer_orbit g) f.

Lemma action_one (Q : {group S}) (f : orbit_hom F P Q) : action 1 f = f.
Proof.
rewrite /action outer_orbit_one.
exact: (@Category.compose_id_left (orbit_category F) P Q f).
Qed.

Lemma action_mul (Q : {group S}) g h (f : orbit_hom F P Q) :
  g \in G -> h \in G -> action (g*h) f = action g (action h f).
Proof.
move=> Gg Gh; rewrite /action outer_orbit_mul //.
exact: (@Category.compose_assoc (orbit_category F) P P P Q (outer_orbit g) (outer_orbit h) f).
Qed.

Definition stabilizer_set (Q : {group S}) (f : orbit_hom F P Q) :=
  [set g in G | action g f == f].

Lemma stabilizer_group_set (Q : {group S}) (f : orbit_hom F P Q) :
  group_set (stabilizer_set f).
Proof.
apply/group_setP; split.
- by apply/setIdP; split; [exact: group1 | rewrite action_one].
- move=> g h /setIdP[Gg /eqP eg] /setIdP[Gh /eqP eh].
  apply/setIdP; split; first exact: groupM Gg Gh.
  by apply/eqP; rewrite action_mul // eh eg.
Qed.

Definition stabilizer (Q : {group S}) (f : orbit_hom F P Q) : {group coset_of (inner P)} :=
  group (stabilizer_group_set f).

Lemma stabilizer_sub (Q : {group S}) (f : orbit_hom F P Q) : stabilizer f \subset G.
Proof. by apply/subsetP=> g /setIdP[]. Qed.

Lemma stabilizer_coset_iff (Q : {group S}) (f : DPFusionSystem.arrow F P Q)
    (a : {perm S}) (Aa : a \in A) :
  coset (inner P) a \in stabilizer (orbit_class f) <->
  exists n : S, n \in Q /\ {in P, forall x, DPFusion.map_fun (val f) (a x) = (DPFusion.map_fun (val f) x)^n}.
Proof.
have Ga : coset (inner P) a \in G := mem_quotient (inner P) Aa.
split.
- move=> /setIdP[_ /eqP e].
  rewrite /action outer_orbit_coset // /aut_orbit orbit_compose_class in e.
  have [n [Qn hn]] := proj1 (orbit_class_eq_iff _ _) (esym e).
  exists n; split=> // x Px.
  have h := hn x Px.
  change (DPFusion.compose (aut_map F P a) (val f) x = (DPFusion.map_fun (val f) x)^n) in h.
  by rewrite DPFusion.compose_in // aut_mapE // in h.
- move=> [n [Qn hn]]; apply/setIdP; split=> //; apply/eqP.
  rewrite /action outer_orbit_coset // /aut_orbit orbit_compose_class.
  symmetry; apply/orbit_class_eq/exists_inP; exists n=> //.
  apply/forall_inP=> x Px; apply/eqP.
  change (DPFusion.compose (aut_map F P a) (val f) x = (DPFusion.map_fun (val f) x)^n).
  by rewrite DPFusion.compose_in // aut_mapE // hn.
Qed.

End Action.
End DPFusionOuterAction.



