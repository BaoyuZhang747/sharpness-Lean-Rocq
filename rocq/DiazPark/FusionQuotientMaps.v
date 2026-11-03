From mathcomp Require Import all_ssreflect all_fingroup center.
From DiazPark Require Import FusionMaps FusionSystems GroupQuotientInfrastructure.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotient.

Section Descent.
Variable S : finGroupType.
Variable Z : {group S}.
Hypothesis nZ : Z <| [set: S]%G.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Hypothesis sZP : Z \subset P.
Hypothesis fixesZ : {in Z, f =1 id}.

Lemma quotient_normalizer_all x : x \in 'N(Z).
Proof. by apply: (subsetP (normal_norm nZ)); rewrite inE. Qed.

Definition projected_function (x : S) := coset Z (f x).

Lemma projected_morphic : {in P &, {morph projected_function : x y / x * y}}.
Proof.
move=> x y Px Py; rewrite /projected_function DPFusion.map_mul //.
by rewrite morphM ?quotient_normalizer_all.
Qed.

Canonical projected_morphism := Morphism projected_morphic.

Lemma projected_kernel : 'ker projected_morphism = Z.
Proof.
apply/setP=> x; apply/idP/idP.
- move=> /morphpreP[Px /set1P hx].
  have fxZ : f x \in Z := coset_idr (quotient_normalizer_all _) hx.
  have Pfx : f x \in P := subsetP sZP _ fxZ.
  have eqx : x = f x.
    apply: (DPFusion.map_injective (f := f) Px Pfx).
    by rewrite (fixesZ fxZ).
  by rewrite eqx.
- move=> Zx; apply/morphpreP; split; first exact: subsetP sZP x Zx.
  apply/set1P; rewrite /= /projected_function (fixesZ Zx).
  exact: coset_id Zx.
Qed.

Lemma projected_kernel_contains : 'ker (coset Z) \subset 'ker projected_morphism.
Proof. by rewrite projected_kernel ker_coset. Qed.

Lemma quotient_source_normalizes : P \subset 'N(Z).
Proof. exact: subset_trans (subsetT P) (normal_norm nZ). Qed.

Definition quotient_morphism : {morphism P / Z >-> coset_of Z} :=
  factm_morphism projected_kernel_contains quotient_source_normalizes.

Lemma quotient_morphismE x : x \in P ->
  quotient_morphism (coset Z x) = coset Z (f x).
Proof. exact: factmE. Qed.

Lemma quotient_morphism_injective : 'injm quotient_morphism.
Proof. apply/injm_factmP; by rewrite projected_kernel ker_coset. Qed.

Lemma quotient_morphism_range : quotient_morphism @* (P / Z) \subset Q / Z.
Proof.
apply/subsetP=> y /morphimP[q qP _ ->].
have /morphimP[x _ Px ->] := qP.
rewrite quotient_morphismE //.
apply: mem_quotient.
exact: DPFusion.map_into Px.
Qed.

Definition quotient_map : DPFusion.map (P / Z)%G (Q / Z)%G :=
  DPFusion.of_morphism quotient_morphism_injective quotient_morphism_range.

Lemma quotient_mapE x : x \in P ->
  quotient_map (coset Z x) = coset Z (f x).
Proof.
move=> Px; rewrite DPFusion.of_morphism_in ?mem_quotient //.
exact: quotient_morphismE.
Qed.

End Descent.

Section Center.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

(** The manuscript's actual extension definition of a central subgroup. *)
Record central (Z : {group S}) : Prop := Central {
  central_sub_center : Z \subset 'Z([set: S]);
  central_extension : forall (P Q : {group S}) (f : DPFusion.map P Q),
    DPFusionSystem.allowed F f ->
    exists fhat : DPFusion.map (P <*> Z)%G (Q <*> Z)%G,
      DPFusionSystem.allowed F fhat /\ {in P, fhat =1 f} /\ {in Z, fhat =1 id}
}.

Lemma central_normal Z : central Z -> Z <| [set: S]%G.
Proof. move=> cZ; exact: sub_center_normal (central_sub_center cZ). Qed.

Lemma central_fixes Z (cZ : central Z) (P Q : {group S})
    (f : DPFusion.map P Q) :
  Z \subset P -> DPFusionSystem.allowed F f -> {in Z, f =1 id}.
Proof.
move=> sZP hf.
have [fhat [_ [hext hfix]]] := central_extension cZ hf.
move=> z Zz; rewrite -(hext z (subsetP sZP z Zz)).
exact: hfix.
Qed.

End Center.
End DPFusionQuotient.
