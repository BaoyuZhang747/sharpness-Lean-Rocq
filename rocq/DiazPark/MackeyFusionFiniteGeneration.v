From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category ModuleInfrastructure MackeyModuleCarriers MackeyStructures
  MackeyGenerated MackeyFiniteGeneration FusionMaps FusionSystems FusionOrbit FusionMackeyShape.

(** A finite labelled family in arbitrary-valued fusion Mackey coefficients
    generates a subfunctor with finitely generated values. Finiteness is
    imposed only on the seed family and the actual fusion indexing category. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPMackeyFinite.
Section FiniteGenerators.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).
Variable I : finType.
Variable source : I -> {group S}.
Variable seed : forall i, mackey_value M (source i).

Definition labelled_seed P (x : mackey_value M P) :=
  exists i : I, exists h : source i = P,
    eq_rect (source i) (mackey_value M) (seed i) P h = x.

Definition finitely_generated_mackey := generated_mackey (@labelled_seed).

Lemma finite_seed_contains i :
    subfunctor_value finitely_generated_mackey (source i) (seed i).
Proof. apply: generated_contains; exists i, (erefl (source i)); reflexivity. Qed.

Definition normal_index P : finType :=
  [the finType of {i : I & {A : [the finType of {group S}] &
    [the finType of
      (DPFusionOrbit.orbit_hom F A (source i) * DPFusionOrbit.orbit_hom F A P)%type]}}].

Definition finite_normal_value P (j : normal_index P) : mackey_value M P :=
  match j with existT i (existT A ab) =>
    mackey_push M ab.2 (mackey_pull M ab.1 (seed i)) end.

Lemma finite_normal_mem P (j : normal_index P) :
    subfunctor_value finitely_generated_mackey P (finite_normal_value j).
Proof.
case: j => i [A [a b]]; apply: span_generator.
exists (source i), A, a, b, (seed i); split=> //.
exists i, (erefl (source i)); reflexivity.
Qed.

Lemma finite_normal_complete P y :
    @normal_generator R (DPFusionOrbit.orbit_category F)
      (DPFusionMackey.fusion_mackey_shape F) M (@labelled_seed) P y ->
    exists j : normal_index P, finite_normal_value j = y.
Proof.
move=> [Q [A [a [b [x [[i [h he]] hx]]]]]].
subst Q; simpl in he; subst x.
exists (existT _ i (existT _ A (a,b))); exact hx.
Qed.


Theorem generated_values_finitely_generated P :
    module_finitely_generated
      [the lmodType R of submodule_carrier (subfunctor_value finitely_generated_mackey P)].
Proof.
refine (@finite_spanning_submodule R (mackey_value M P)
  (subfunctor_value finitely_generated_mackey P)
  [the finType of normal_index P] (@finite_normal_value P) (@finite_normal_mem P) _).
move=> x hx; apply: (@span_mono R (mackey_value M P)
  (@normal_generator R (DPFusionOrbit.orbit_category F)
    (DPFusionMackey.fusion_mackey_shape F) M (@labelled_seed) P)) _ hx.
exact: finite_normal_complete.
Qed.

End FiniteGenerators.
End DPMackeyFinite.




