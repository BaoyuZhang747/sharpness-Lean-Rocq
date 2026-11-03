(** Baer's extension criterion, with actual left ideals and linear maps.
    The maximal partial map is obtained from the proved Zorn theorem. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import CategoryModules ModuleInfrastructure MackeyModuleCarriers
  ModuleInjectives ModulePartialMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Baer.
Variable R : pzRingType.
Variable J : lmodType R.

Definition module_baer_condition : Prop :=
  forall N : module_subspace [the lmodType R of R^o],
  forall f : module_hom [the lmodType R of submodule_carrier N] J,
  exists g : module_hom [the lmodType R of R^o] J,
    forall z, g (submodule_val z) = f z.

Section OneGenerator.
Variable B : lmodType R.
Variable p : @graph_type R B J.
Variable x : B.

Definition graph_scalar_ideal : module_subspace [the lmodType R of R^o].
Proof.
  refine (@ModuleSubspace R [the lmodType R of R^o]
    (fun a => exists y, graph_space p ((a : R) *: x, y)) _ _ _).
  - exists 0. rewrite scale0r. exact (subspace_zero (graph_space p)).
  - intros a b [y hy] [z hz]. exists (y+z). rewrite scalerDl.
    exact (@subspace_add R _ (graph_space p) _ _ hy hz).
  - intros a b [y hy]. exists (a *: y).
    change (graph_space p ((a * (b : R)) *: x, a *: y)).
    rewrite <- scalerA. exact (@subspace_scale R _ (graph_space p) a _ hy).
Defined.

Definition graph_ideal_value (a : submodule_carrier graph_scalar_ideal) : J :=
  proj1_sig (constructive_indefinite_description (submodule_val_mem a)).

Lemma graph_ideal_value_spec (a : submodule_carrier graph_scalar_ideal) :
    graph_space p ((submodule_val a : R) *: x, graph_ideal_value a).
Proof. exact (proj2_sig (constructive_indefinite_description (submodule_val_mem a))). Qed.

Lemma graph_ideal_value_linear : linear graph_ideal_value.
Proof.
  intros r a b.
  apply (@graph_functional R B J p ((submodule_val (r *: a + b) : R) *: x)).
  - apply graph_ideal_value_spec.
  - have hv := @submodule_val_linear R [the lmodType R of R^o] graph_scalar_ideal r a b.
    change ((submodule_val (r *: a + b) : R) = r * (submodule_val a : R) + (submodule_val b : R)) in hv.
    rewrite hv scalerDl -scalerA.
    exact (@subspace_add R _ (graph_space p) _ _
      (@subspace_scale R _ (graph_space p) r _ (graph_ideal_value_spec a))
      (graph_ideal_value_spec b)).
Qed.

Definition graph_ideal_hom :
    module_hom [the lmodType R of submodule_carrier graph_scalar_ideal] J :=
  exist _ graph_ideal_value graph_ideal_value_linear.

Variable g : module_hom [the lmodType R of R^o] J.
Hypothesis gext : forall z, g (submodule_val z) = graph_ideal_hom z.

Lemma graph_ideal_agrees (a : R) y : graph_space p (a *: x, y) -> g a = y.
Proof.
  intro h. pose (z := @submodule_in R [the lmodType R of R^o] graph_scalar_ideal a
    (ex_intro _ y h)).
  transitivity (graph_ideal_hom z).
  - exact (gext z).
  - exact (@graph_functional R B J p (a *: x) (graph_ideal_hom z) y
      (graph_ideal_value_spec z) h).
Qed.

Definition extended_graph_space : module_subspace [the lmodType R of (B * J)%type].
Proof.
  refine (@ModuleSubspace R [the lmodType R of (B * J)%type]
    (fun v => exists u y (a : R), graph_space p (u,y) /\ (u + a *: x, y + g a) = v) _ _ _).
  - exists 0, 0, 0. split. exact (subspace_zero (graph_space p)).
    by rewrite scale0r module_hom_zero !addr0.
  - intros v w [u [y [a [ha <-]]]] [u' [y' [b [hb <-]]]].
    exists (u+u'), (y+y'), (a+b). split.
    + exact (@subspace_add R _ (graph_space p) _ _ ha hb).
    + rewrite scalerDl module_hom_add. congr (_, _); apply addrACA.
  - intros r v [u [y [a [ha <-]]]].
    exists (r *: u), (r *: y), (r*a). split.
    + exact (@subspace_scale R _ (graph_space p) r _ ha).
    + change ((r *: u + (r*a) *: x, r *: y + g (r *: (a : R^o))) =
        (r *: (u + a *: x), r *: (y + g a))).
      by rewrite module_hom_scale !scalerDr scalerA.
Defined.

Lemma extended_graph_functional v w w' :
    extended_graph_space (v,w) -> extended_graph_space (v,w') -> w = w'.
Proof.
  intros [u [y [a [hp he]]]] [u' [y' [b [hp' he']]]].
  have hv : u + a *: x = u' + b *: x.
  { transitivity v. exact (f_equal fst he). symmetry. exact (f_equal fst he'). }
  have hxy : (a-b) *: x = u'-u.
  { rewrite scalerBl. apply: (addrI u).
    by rewrite subrKC addrA hv addrK. }
  have hgraph : graph_space p ((a-b) *: x,y'-y).
  { rewrite hxy. exact (@subspace_sub R _ (graph_space p) _ _ hp' hp). }
  have hg := graph_ideal_agrees hgraph.
  rewrite module_hom_sub in hg.
  have hw : y + g a = y' + g b.
  { rewrite -(subrK (g b) (g a)) hg addrA.
    by rewrite subrKC. }
  transitivity (y + g a). symmetry. exact (f_equal snd he).
  transitivity (y' + g b). exact hw. exact (f_equal snd he').
Qed.

Definition extended_graph : @graph_type R B J :=
  @LinearGraph R B J extended_graph_space extended_graph_functional.

Lemma extended_graph_contains : graph_le p extended_graph.
Proof.
  intros [u y] h. exists u, y, 0. split. exact h.
  by rewrite scale0r module_hom_zero !addr0.
Qed.

Lemma extended_graph_generator : graph_space extended_graph (x,g 1).
Proof.
  exists 0, 0, 1. split. exact (subspace_zero (graph_space p)).
  by rewrite scale1r !add0r.
Qed.

End OneGenerator.

Theorem baer_implies_injective : module_baer_condition -> module_injective J.
Proof.
  intros baer U B m mi f.
  destruct (maximal_linear_extension mi f) as [p [hp hmax]].
  assert (forall x : B, exists y, graph_space p (x,y)) as hfull.
  { intro x. destruct (baer (graph_scalar_ideal p x) (graph_ideal_hom p x)) as [g hg].
    pose (q := @extended_graph B p x g hg).
    have hpq : graph_le p q := @extended_graph_contains B p x g hg.
    have hqp : graph_le q p.
    { apply hmax. intro u. apply hpq. exact (hp u). exact hpq. }
    exists (g 1). apply hqp. exact (@extended_graph_generator B p x g hg). }
  pose (value := fun x => proj1_sig (constructive_indefinite_description (hfull x))).
  have value_spec : forall x, graph_space p (x,value x).
  { intro x. exact (proj2_sig (constructive_indefinite_description (hfull x))). }
  have vl : linear value.
  { intros a x y. apply (@graph_functional R B J p (a *: x+y)).
    - apply value_spec.
    - exact (@subspace_add R _ (graph_space p) _ _
        (@subspace_scale R _ (graph_space p) a _ (value_spec x)) (value_spec y)). }
  exists (exist _ value vl). intro u.
  exact (@graph_functional R B J p (m u) (value (m u)) (f u) (value_spec (m u)) (hp u)).
Qed.

Theorem injective_implies_baer : module_injective J -> module_baer_condition.
Proof.
  intros h N f.
  exact (h [the lmodType R of submodule_carrier N] [the lmodType R of R^o]
    (exist _ (@submodule_val R [the lmodType R of R^o] N)
      (@submodule_val_linear R [the lmodType R of R^o] N))
    (@submodule_val_injective R [the lmodType R of R^o] N) f).
Qed.

Theorem module_baer_criterion : module_injective J <-> module_baer_condition.
Proof. split. apply injective_implies_baer. apply baer_implies_injective. Qed.

End Baer.
