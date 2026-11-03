From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp vector.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers
  MackeyModuleMaps MackeyModuleQuotient MackeyFiniteGeneration ModuleFiniteDimensional.

(** Arbitrary Prop-valued submodules of a finite-dimensional module are
    finitely generated.  Decidable membership and a basis are consequences,
    not additional hypotheses on the submodule. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section FiniteSubmodules.
Variable K : fieldType.
Variable V : vectType K.

Lemma module_span_native (s : seq V) x :
    module_span (fun y => y \in s) x <-> x \in <<s>>%VS.
Proof.
split.
- move=> h; elim: h => [y hy| |y z hy ihy hz ihz|a y hy ihy].
  + exact: memv_span.
  + exact: mem0v.
  + exact: memvD.
  + exact: memvZ.
- move=> hx; have he := coord_span (X := in_tuple s) hx.
  rewrite he; elim/big_rec: _ => [|i z _ hz].
  + exact: span_zero.
  + apply: span_add _ hz; apply: span_scale; apply: span_generator.
    exact: memt_nth.
Qed.

Lemma finite_dimensional_finitely_generated :
    module_finitely_generated V.
Proof.
exists (vbasis fullv) => x; apply/module_span_native.
by rewrite (span_basis (vbasisP fullv)) memvf.
Qed.

Variable N : module_subspace V.

Definition submodule_span_rank (n : nat) : bool :=
  `[< exists s : seq V, (forall x, x \in s -> N x) /\ \dim <<s>> = n >].

Lemma submodule_span_rank_exists : exists n, submodule_span_rank n.
Proof.
exists 0%N; apply/asboolP; exists [::]; split.
- by move=> x; rewrite in_nil.
- by rewrite span_nil dimv0.
Qed.

Lemma submodule_span_rank_bound n : submodule_span_rank n -> (n <= dim V)%N.
Proof.
move/asboolP=> [s [_ <-]]; rewrite -dimvf; exact: dimvS (subvf _).
Qed.

Lemma submodule_has_finite_spanning_sequence :
    exists s : seq V, (forall x, x \in s -> N x) /\
      forall x, N x -> module_span (fun y => y \in s) x.
Proof.
have [n /asboolP[s [hs hdim]] hmax] :=
  @ex_maxnP submodule_span_rank (dim V)
    submodule_span_rank_exists submodule_span_rank_bound.
exists s; split=> // x hx; apply/module_span_native.
have hxs : forall y, y \in x :: s -> N y.
  move=> y; rewrite in_cons; move/orP=> [/eqP ->|hy]; [exact hx|exact: hs].
have hdim' : (\dim <<x :: s>> <= \dim <<s>>)%N.
  rewrite hdim; apply: hmax; apply/asboolP; exists (x :: s); by split.
have hsub : (<<s>> <= <<x :: s>>)%VS.
  by rewrite span_cons; exact: addvSr.
have he : (<<s>> == <<x :: s>>)%VS.
  by rewrite eqEdim hsub hdim'.
rewrite (eqP he); exact: memv_span (mem_head x s).
Qed.

Lemma finite_dimensional_submodule_finitely_generated :
    module_finitely_generated [the lmodType K of submodule_carrier N].
Proof.
have [s [hs hspan]] := submodule_has_finite_spanning_sequence.
pose v (i : 'I_(size s)) := nth 0 s i.
have hv i : N (v i) by apply: hs; exact: mem_nth (ltn_ord i).
apply: (finite_spanning_submodule hv) => x hx.
have hmap : forall y, y \in s -> exists i : 'I_(size s), v i = y.
  move=> y /(nthP 0)[i hi <-]; by exists (Ordinal hi).
exact (@span_mono K V (fun y => y \in s)
  (fun y => exists i : 'I_(size s), v i = y) hmap x (hspan x hx)).
Qed.

Definition finite_submodule_vect : vectType K :=
  finitely_generated_vect finite_dimensional_submodule_finitely_generated.

Lemma finite_submodule_vect_same_carrier :
    (finite_submodule_vect : Type) = submodule_carrier N.
Proof. reflexivity. Qed.

Lemma finite_dimensional_quotient_finitely_generated :
    module_finitely_generated [the lmodType K of module_quotient N].
Proof.
exact (@finitely_generated_surjective_image K V
  [the lmodType K of module_quotient N]
  (quotient_pi N : {linear V -> module_quotient N})
  (@quotient_pi_surjective K V N) finite_dimensional_finitely_generated).
Qed.

Definition finite_quotient_vect : vectType K :=
  finitely_generated_vect finite_dimensional_quotient_finitely_generated.

Lemma finite_quotient_vect_same_carrier :
    (finite_quotient_vect : Type) = module_quotient N.
Proof. reflexivity. Qed.

End FiniteSubmodules.

Section FinitelyGeneratedSubmodules.
Variable K : fieldType.
Variable V : lmodType K.
Variable hfg : module_finitely_generated V.
Variable N : module_subspace V.

Theorem field_finitely_generated_submodule :
    module_finitely_generated [the lmodType K of submodule_carrier N].
Proof.
pose U := chosen_finite_model hfg.
pose f := chosen_model_map hfg.
pose P := linear_preimage f N.
have hf : forall x, P x -> N (f x) by move=> x hx; exact hx.
pose g := @submodule_map K U V f P N hf.
have hg : forall y, exists x, g x = y.
  move=> y.
  have hp : P (chosen_model_inverse hfg (submodule_val y)).
    change (N (chosen_model_map hfg
      (chosen_model_inverse hfg (submodule_val y)))).
    rewrite chosen_model_inverseK; exact: submodule_val_mem.
  exists (@submodule_in K U P _ hp); apply: submodule_val_injective.
  change (chosen_model_map hfg
    (chosen_model_inverse hfg (submodule_val y)) = submodule_val y).
  exact: chosen_model_inverseK.
exact (@finitely_generated_surjective_image K
  [the lmodType K of submodule_carrier P]
  [the lmodType K of submodule_carrier N] g hg
  (@finite_dimensional_submodule_finitely_generated K U P)).
Qed.

Theorem field_finitely_generated_quotient :
    module_finitely_generated [the lmodType K of module_quotient N].
Proof.
exact (@finitely_generated_surjective_image K V
  [the lmodType K of module_quotient N]
  (quotient_pi N : {linear V -> module_quotient N})
  (@quotient_pi_surjective K V N) hfg).
Qed.

End FinitelyGeneratedSubmodules.
