(** Maximal extensions of module homomorphisms, proved using MathComp's
    theorem of Zorn. A partial map is a functional linear graph; no values
    outside its domain are stored or identified. *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp wochoice.
From DiazPark Require Import CategoryModules ModuleInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section LinearGraphs.
Variable R : pzRingType.
Variables B J : lmodType R.

Record linear_graph := LinearGraph {
  graph_space : module_subspace [the lmodType R of (B * J)%type];
  graph_functional : forall x y z, graph_space (x,y) -> graph_space (x,z) -> y = z
}.

Definition graph_type := classicType linear_graph.
HB.instance Definition _ := Choice.on graph_type.

Definition graph_le (p q : graph_type) : Prop :=
  forall v, graph_space p v -> graph_space q v.

Definition graph_rel : rel graph_type := fun p q => `[< graph_le p q >].

Lemma graph_rel_refl : reflexive graph_rel.
Proof. intro p. apply/asboolP. intros v hv. exact hv. Qed.

Lemma graph_rel_trans : transitive graph_rel.
Proof.
  move=> q p s /asboolP hp /asboolP hq. apply/asboolP.
  intros v hv. apply hq. apply hp. exact hv.
Qed.

Definition graph_contains (U : lmodType R) (m : module_hom U B) (f : module_hom U J)
    (p : graph_type) : Prop := forall u, graph_space p (m u, f u).

Definition initial_graph_space (U : lmodType R) (m : module_hom U B)
    (f : module_hom U J) : module_subspace [the lmodType R of (B * J)%type].
Proof.
  refine (@ModuleSubspace R [the lmodType R of (B * J)%type]
    (fun v => exists u, (m u, f u) = v) _ _ _).
  - exists 0. by rewrite !module_hom_zero.
  - intros x y [u <-] [v <-]. exists (u+v). by rewrite !module_hom_add.
  - intros a x [u <-]. exists (a *: u). by rewrite !module_hom_scale.
Defined.

Definition initial_graph (U : lmodType R) (m : module_hom U B)
    (mi : injective m) (f : module_hom U J) : graph_type.
Proof.
  refine (@LinearGraph (initial_graph_space m f) _).
    intros x y z [u hu] [v hv].
    assert (u = v) as e.
    { apply mi. transitivity x. exact (f_equal fst hu). symmetry. exact (f_equal fst hv). }
    subst v. transitivity (f u). symmetry. exact (f_equal snd hu). exact (f_equal snd hv).
Defined.

Lemma initial_graph_contains (U : lmodType R) (m : module_hom U B)
    (mi : injective m) (f : module_hom U J) :
    graph_contains m f (initial_graph mi f).
Proof. intro u. exists u. reflexivity. Qed.

Section ChainUnion.
Variable X : {pred graph_type}.
Hypothesis Xchain : chain graph_rel X.
Variable p0 : graph_type.
Hypothesis Xp0 : X p0.

Definition union_graph_space : module_subspace [the lmodType R of (B * J)%type].
Proof.
  refine (@ModuleSubspace R [the lmodType R of (B * J)%type]
    (fun v => exists p, X p /\ graph_space p v) _ _ _).
  - exists p0. split. exact Xp0. apply subspace_zero.
  - intros x y [p [hp hx]] [q [hq hy]].
    destruct (orP (@Xchain p q hp hq)) as [hpq|hqp].
    + exists q. split. exact hq. apply subspace_add.
      exact ((elimT (asboolP (graph_le p q)) hpq) _ hx). exact hy.
    + exists p. split. exact hp. apply subspace_add. exact hx.
      exact ((elimT (asboolP (graph_le q p)) hqp) _ hy).
  - intros a v [p [hp hv]]. exists p. split. exact hp.
    exact (@subspace_scale R _ (graph_space p) a v hv).
Defined.

Definition union_graph : graph_type.
Proof.
  refine (@LinearGraph union_graph_space _).
  intros x y z [p [hp hy]] [q [hq hz]].
  destruct (orP (@Xchain p q hp hq)) as [hpq|hqp].
  - apply (@graph_functional q x y z).
    exact ((elimT (asboolP (graph_le p q)) hpq) _ hy). exact hz.
  - apply (@graph_functional p x y z). exact hy.
    exact ((elimT (asboolP (graph_le q p)) hqp) _ hz).
Defined.

Lemma union_graph_upper p : X p -> graph_le p union_graph.
Proof. intros hp v hv. exists p. split; assumption. Qed.

End ChainUnion.

Theorem maximal_linear_extension (U : lmodType R) (m : module_hom U B)
    (mi : injective m) (f : module_hom U J) :
    exists p : graph_type, graph_contains m f p /\
      forall q : graph_type, graph_contains m f q -> graph_le p q -> graph_le q p.
Proof.
  pose (S := fun p : graph_type => `[< graph_contains m f p >]).
  assert ({in S, reflexive graph_rel}) as rr.
  { intros p hp. apply graph_rel_refl. }
  assert ({in S & &, transitive graph_rel}) as rt.
  { intros p q s hp hq hs. apply graph_rel_trans. }
  assert ({in <= S, forall X, wo_chain graph_rel X ->
    exists2 z, z \in S & upper_bound graph_rel X z}) as ub.
  { intros X XS Xwo.
    destruct (pselect (exists p : graph_type, X p)) as [[p0 hp0]|hempty].
    - pose (g := @union_graph X (@wo_chainW graph_type graph_rel X Xwo) p0 hp0).
      exists g.
      + apply/asboolP. intro u. exists p0. split. exact hp0.
        have hpS := XS p0 hp0. move/asboolP: hpS => hpS. exact (hpS u).
      + intros p hp. apply/asboolP. apply union_graph_upper. exact hp.
    - exists (initial_graph mi f).
      + apply/asboolP. exact (initial_graph_contains mi f).
      + intros p hp. exfalso. apply hempty. exists p. exact hp. }
  destruct (@Zorn's_lemma graph_type graph_rel S rr rt ub) as [p hp hm].
  exists p. split.
  - exact (elimT (asboolP _) hp).
  - intros q hq hpq. apply (elimT (asboolP _)).
    apply hm. exact (introT (asboolP _) hq). exact (introT (asboolP _) hpq).
Qed.

End LinearGraphs.
