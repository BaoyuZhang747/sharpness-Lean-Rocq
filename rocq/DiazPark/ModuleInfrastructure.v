From mathcomp Require Import all_ssreflect all_algebra.

(** Arbitrary modules, including over the zero ring. No finite-dimensional
    vector-space structure is required anywhere in this file. Submodules
    have Prop-valued membership, so no decidability of membership is assumed. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section ArbitraryModules.
Variable R : pzRingType.

Record module_subspace (V : lmodType R) := ModuleSubspace {
  subspace_mem : V -> Prop;
  subspace_zero : subspace_mem 0;
  subspace_add : forall x y, subspace_mem x -> subspace_mem y ->
    subspace_mem (x + y);
  subspace_scale : forall a x, subspace_mem x -> subspace_mem (a *: x)
}.

Coercion subspace_mem : module_subspace >-> Funclass.

Arguments subspace_zero {V} N : rename.
Arguments subspace_add {V N x y} _ _ : rename.
Arguments subspace_scale {V N} a {x} _ : rename.

Lemma subspace_opp (V : lmodType R) (N : module_subspace V) x :
  N x -> N (- x).
Proof. move=> hx; rewrite -scaleN1r; exact (@subspace_scale V N (-1) x hx). Qed.

Lemma subspace_sub (V : lmodType R) (N : module_subspace V) x y :
  N x -> N y -> N (x - y).
Proof.
move=> hx hy.
exact (@subspace_add V N x (-y) hx (@subspace_opp V N y hy)).
Qed.

Definition subspace_le (V : lmodType R) (N P : module_subspace V) :=
  forall x, N x -> P x.

Definition subspace_zero_space (V : lmodType R) : module_subspace V.
Proof.
refine (@ModuleSubspace V (fun x => x = 0) _ _ _).
- reflexivity.
- by move=> x y -> ->; rewrite addr0.
- by move=> a x ->; rewrite scaler0.
Defined.

Definition subspace_full (V : lmodType R) : module_subspace V.
Proof. exact (@ModuleSubspace V (fun _ => True) I (fun _ _ _ _ => I)
  (fun _ _ _ => I)). Defined.

Definition subspace_inter (V : lmodType R) (N P : module_subspace V) :
  module_subspace V.
Proof.
refine (@ModuleSubspace V (fun x => N x /\ P x) _ _ _).
- exact: (conj (subspace_zero N) (subspace_zero P)).
- move=> x y [hxN hxP] [hyN hyP]; split.
  + exact: subspace_add hxN hyN.
  + exact: subspace_add hxP hyP.
- move=> a x [hxN hxP]; split.
  + exact (@subspace_scale V N a x hxN).
  + exact (@subspace_scale V P a x hxP).
Defined.

Definition subspace_intersection (V : lmodType R) (I : Type)
    (N : I -> module_subspace V) : module_subspace V.
Proof.
refine (@ModuleSubspace V (fun x => forall i, N i x) _ _ _).
- exact: (fun i => subspace_zero (N i)).
- move=> x y hx hy i; exact: subspace_add (hx i) (hy i).
- move=> a x hx i; exact (@subspace_scale V (N i) a x (hx i)).
Defined.

Definition linear_kernel (V W : lmodType R) (f : {linear V -> W}) :
  module_subspace V.
Proof.
refine (@ModuleSubspace V (fun x => f x = 0) _ _ _).
- exact: linear0.
- by move=> x y hx hy; rewrite linearD hx hy addr0.
- by move=> a x hx; rewrite linearZ /= hx scaler0.
Defined.

Definition linear_image (V W : lmodType R) (f : {linear V -> W}) :
  module_subspace W.
Proof.
refine (@ModuleSubspace W (fun y => exists x, f x = y) _ _ _).
- exists 0; exact: linear0.
- move=> y z [x <-] [w <-]; exists (x + w); exact: linearD.
- move=> a y [x <-]; exists (a *: x); by rewrite linearZ.
Defined.

Definition linear_preimage (V W : lmodType R) (f : {linear V -> W})
    (N : module_subspace W) : module_subspace V.
Proof.
refine (@ModuleSubspace V (fun x => N (f x)) _ _ _).
- by rewrite linear0; exact: subspace_zero.
- move=> x y hx hy; rewrite linearD; exact: subspace_add hx hy.
- move=> a x hx; rewrite linearZ /=; exact (@subspace_scale W N a (f x) hx).
Defined.

Inductive module_span (V : lmodType R) (X : V -> Prop) : V -> Prop :=
| span_generator x of X x : module_span X x
| span_zero : module_span X 0
| span_add x y of module_span X x & module_span X y : module_span X (x + y)
| span_scale a x of module_span X x : module_span X (a *: x).

Definition span_subspace (V : lmodType R) (X : V -> Prop) : module_subspace V.
Proof. exact (@ModuleSubspace V (module_span X) (@span_zero V X)
  (@span_add V X) (@span_scale V X)). Defined.

Lemma span_least (V : lmodType R) (X : V -> Prop) (N : module_subspace V) :
  (forall x, X x -> N x) -> forall x, module_span X x -> N x.
Proof.
move=> hX x hx; elim: hx => [y hy| |y z hy ihy hz ihz|a y hy ihy].
- exact: hX hy.
- exact: subspace_zero.
- exact: subspace_add ihy ihz.
- exact (@subspace_scale V N a y ihy).
Qed.

Lemma span_mono (V : lmodType R) (X Y : V -> Prop) :
  (forall x, X x -> Y x) -> forall x, module_span X x -> module_span Y x.
Proof.
move=> h; apply: (@span_least V X (span_subspace Y)).
by move=> x hx; apply: span_generator; apply: h hx.
Qed.

Lemma span_linear_image (V W : lmodType R) (f : {linear V -> W})
    (X : V -> Prop) x : module_span X x ->
  module_span (fun y => exists v, X v /\ f v = y) (f x).
Proof.
move=> hx; elim: hx => [y hy| |y z hy ihy hz ihz|a y hy ihy].
- apply: span_generator; by exists y.
- rewrite linear0; exact: span_zero.
- rewrite linearD; exact: span_add ihy ihz.
- rewrite linearZ /=; exact (@span_scale W _ a (f y) ihy).
Qed.

(** Every element of a span uses finitely many generators, even when the
    ambient module and the original generating collection are arbitrary. *)
Lemma span_finite_support (V : lmodType R) (X : V -> Prop) x :
  module_span X x -> exists s : seq V,
    (forall y, y \in s -> X y) /\ module_span (fun y => y \in s) x.
Proof.
move=> hx; elim: hx => [y hy| |y z hy [s [hs hsy]] hz [t [ht htz]]|
  a y hy [s [hs hsy]]].
- exists [:: y]; split.
  + by move=> z; rewrite in_cons in_nil orbF => /eqP ->.
  + apply: span_generator; by rewrite in_cons eqxx.
- exists [::]; split; first by move=> y; rewrite in_nil.
  exact: span_zero.
- exists (s ++ t); split.
  + move=> v; rewrite mem_cat => /orP [hv|hv].
    * exact: hs hv.
    * exact: ht hv.
  + apply: span_add.
    * apply: (@span_mono V (fun v => v \in s)) hsy.
      by move=> v hv; rewrite mem_cat hv.
    * apply: (@span_mono V (fun v => v \in t)) htz.
      by move=> v hv; rewrite mem_cat hv orbT.
- exists s; split=> //; exact (@span_scale V _ a y hsy).
Qed.

Definition module_finitely_generated (V : lmodType R) :=
  exists s : seq V, forall x, module_span (fun y => y \in s) x.

Lemma finitely_generated_surjective_image (V W : lmodType R)
    (f : {linear V -> W}) :
  (forall y, exists x, f x = y) ->
  module_finitely_generated V -> module_finitely_generated W.
Proof.
move=> hf [s hs]; exists [seq f x | x <- s] => y.
have [x <-] := hf y.
apply: (@span_mono W (fun z => exists v, v \in s /\ f v = z)).
- move=> z [v [hv <-]]; exact: map_f.
- exact: span_linear_image (hs x).
Qed.

End ArbitraryModules.

Section ScalarSubmodules.
Variable R : comPzRingType.

Definition scalar_kernel (V : lmodType R) (r : R) : module_subspace V.
Proof.
refine (@ModuleSubspace R V (fun x => r *: x = 0) _ _ _).
- exact: scaler0.
- by move=> x y hx hy; rewrite scalerDr hx hy addr0.
- move=> a x hx; rewrite !scalerA [r * a]mulrC -scalerA hx.
  exact: scaler0.
Defined.

Arguments scalar_kernel {V} r.

Definition scalar_image (V : lmodType R) (r : R) : module_subspace V.
Proof.
refine (@ModuleSubspace R V (fun y => exists x, r *: x = y) _ _ _).
- exists 0; exact: scaler0.
- move=> y z [x <-] [w <-]; exists (x + w); exact: scalerDr.
- move=> a y [x <-]; exists (a *: x).
  by rewrite !scalerA mulrC.
Defined.

Arguments scalar_image {V} r.

Lemma linear_preserves_scalar_kernel (V W : lmodType R)
    (f : {linear V -> W}) (r : R) x :
  scalar_kernel r x -> scalar_kernel r (f x).
Proof. by move=> hx; rewrite /scalar_kernel /= -linearZ hx linear0. Qed.

Lemma linear_preserves_scalar_image (V W : lmodType R)
    (f : {linear V -> W}) (r : R) x :
  scalar_image r x -> scalar_image r (f x).
Proof. by move=> [y <-]; exists (f y); rewrite linearZ. Qed.

End ScalarSubmodules.

Section ModuleExactness.
Variable R : pzRingType.

(** Exactness stated on the actual carrier maps; this will be used to
    install the two scalar subquotient sequences after quotient construction. *)
Definition linear_exact (U V W : lmodType R)
    (f : {linear U -> V}) (g : {linear V -> W}) :=
  forall v, g v = 0 <-> exists u, f u = v.

Lemma linear_exact_composite_zero (U V W : lmodType R)
    (f : {linear U -> V}) (g : {linear V -> W}) :
  linear_exact f g -> forall u, g (f u) = 0.
Proof. move=> h u; apply/(h (f u)); by exists u. Qed.

End ModuleExactness.
