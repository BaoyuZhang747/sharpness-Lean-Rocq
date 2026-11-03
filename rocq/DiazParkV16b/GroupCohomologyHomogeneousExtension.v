(** A normalized equivariant extension of any subgroup homomorphism to
    ambient vertices. It agrees literally on every subgroup element. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazParkV16b Require Import GroupCohomologyHomogeneousProjectiveCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyHomogeneousProjectiveCoordinates.
Local Open Scope group_scope.

Module DPGroupCohomologyHomogeneousExtension.
Section Retraction.
Variable G : finGroupType.
Variable H : {group G}.

Lemma coefficient_left (h : [subg H]) x :
  coefficient H (val h * x) = h * coefficient H x.
Proof.
apply val_inj.
change (val (coefficient H (val h * x)) = val h * val (coefficient H x)).
by rewrite !coefficientE representative_left ?subgP // mulgA.
Qed.

Definition subgroup_vertex_retraction x : [subg H] :=
  coefficient H x * (coefficient H 1)^-1.

Lemma subgroup_vertex_retraction_equivariant (h : [subg H]) x :
  subgroup_vertex_retraction (val h * x) = h * subgroup_vertex_retraction x.
Proof. by rewrite /subgroup_vertex_retraction coefficient_left mulgA. Qed.

Lemma subgroup_vertex_retraction_subgroup (h : [subg H]) :
  subgroup_vertex_retraction (val h) = h.
Proof.
rewrite -{1}(mulg1 (val h)) subgroup_vertex_retraction_equivariant.
by rewrite /subgroup_vertex_retraction mulgV mulg1.
Qed.

End Retraction.

Section Extension.
Variables G K : finGroupType.
Variable H : {group G}.
Variable J : {group K}.
Local Notation HS := [the finGroupType of [subg H]%type].
Local Notation JS := [the finGroupType of [subg J]%type].
Variable e : {morphism [set: HS] >-> JS}.

Definition subgroup_hom_vertex_extension (x : G) : K :=
  val (e (subgroup_vertex_retraction H x)).

Lemma subgroup_hom_vertex_extension_equivariant (h : [subg H]) x :
  subgroup_hom_vertex_extension (val h * x) =
    val (e h) * subgroup_hom_vertex_extension x.
Proof.
rewrite /subgroup_hom_vertex_extension subgroup_vertex_retraction_equivariant
  morphM ?inE //; reflexivity.
Qed.

Lemma subgroup_hom_vertex_extension_subgroup (h : [subg H]) :
  subgroup_hom_vertex_extension (val h) = val (e h).
Proof. by rewrite /subgroup_hom_vertex_extension subgroup_vertex_retraction_subgroup. Qed.

End Extension.
End DPGroupCohomologyHomogeneousExtension.


