From mathcomp Require Import all_boot all_algebra all_fingroup boolp pgroup quotient.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures
  MackeyMinimal MackeyFusionMinimal MackeyGroupAction MackeyGroupActionNormal
  FusionMaps FusionSystems FusionOrbit FusionMackeyShape FusionOuterAutomorphisms
  FusionOuterEndomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionOuter DPFusionOuterEndomorphisms.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPMackeyOuterAction.
Section OuterAction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).
Variable P : {group S}.

Definition outer_right_action : right_linear_action [the finGroupType of [subg (outer_group F P)]%type] (mackey_value M P).
Proof.
refine (@Build_right_linear_action R [the finGroupType of [subg (outer_group F P)]%type] (mackey_value M P)
  (fun g => mackey_push M (@outer_endomorphism S F P g)) _ _).
- move=> x; rewrite outer_endomorphism_one; exact: mackey_push_id.
- move=> a b x; rewrite outer_endomorphism_mul; exact: mackey_push_comp.
Defined.

Lemma outer_action_simple : automorphism_simple_at M P -> action_simple outer_right_action.
Proof.
move=> [hnz hs]; split=> // W hW; apply: hs => e x hx.
have h := hW (@endomorphism_outer S F P (iso_hom e)) x hx.
change (W (mackey_push M
  (@outer_endomorphism S F P (@endomorphism_outer S F P (iso_hom e))) x)) in h.
by rewrite endomorphism_outerK in h.
Qed.

End OuterAction.

Section NormalP.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable K : fieldType.
Variable M : mackey_module K (DPFusionMackey.fusion_mackey_shape F).
Variable P : {group S}.

Theorem simple_outer_normal_p_trivial p (hp : p \in [pchar K])
    (H : {group coset_of (inner P)}) :
    H <| outer_group F P -> p.-group H -> automorphism_simple_at M P ->
    forall g : [subg (outer_group F P)], val g \in H ->
    forall x, mackey_push M (@outer_endomorphism S F P g) x = x.
Proof.
move=> hn hH hs.
pose U := outer_group F P.
pose J : {group [subg U]} := (subg U @* H)%G.
have hJnormal : J <| [set: [subg U]].
  rewrite /J -im_subg; exact: morphim_normal hn.
have hJp : p.-group J := morphim_pgroup (subg U) hH.
have htriv := @simple_action_normal_p_trivial K [the finGroupType of [subg U]%type] (mackey_value M P)
  (outer_right_action M P) p hp J hJnormal hJp (outer_action_simple hs).
move=> g hg x; apply: htriv.
change (g \in subg U @* H).
rewrite -(sgvalK g); apply: mem_morphim; [exact: valP | exact hg].
Qed.

Theorem conjugate_outer_normal_p_trivial
    (Q : {group S}) (leastQ : mackey_least_nonzero M (fun U : {group S} => #|U|) Q)
    (hM : mackey_simple M) (conjQP : DPFusionSystem.conjugate F Q P)
    p (hp : p \in [pchar K]) (H : {group coset_of (inner P)}) :
    H <| outer_group F P -> p.-group H ->
    forall g : [subg (outer_group F P)], val g \in H ->
    forall x, mackey_push M (@outer_endomorphism S F P g) x = x.
Proof.
move=> hn hH.
exact (@simple_outer_normal_p_trivial p hp H hn hH
  (@DPMackeyMinimal.conjugate_automorphism_simple S F K M Q leastQ hM P conjQP)).
Qed.

End NormalP.
End DPMackeyOuterAction.

