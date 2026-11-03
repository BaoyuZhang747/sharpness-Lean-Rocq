From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp vector.
From DiazPark Require Import ModuleInfrastructure.

(** Finite dimension is derived from finite generation of an arbitrary
    field module; it is never an assumption on the global coefficient type. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SpanCons.
Variable R : pzRingType.
Variable V : lmodType R.
Variable v : V.
Variable s : seq V.

Definition cons_decomposition : module_subspace V.
Proof.
refine (@ModuleSubspace R V
  (fun x => exists a : R, exists y : V,
    module_span (fun z => z \in s) y /\ a *: v + y = x) _ _ _).
- exists 0, 0; split; first exact: span_zero.
  by rewrite scale0r addr0.
- move=> x y [a [u [hu <-]]] [b [w [hw <-]]].
  exists (a+b), (u+w); split; first exact: span_add hu hw.
  by rewrite scalerDl addrACA.
- move=> a x [b [u [hu <-]]]; exists (a*b), (a *: u); split.
  + exact: span_scale hu.
  + by rewrite scalerDr scalerA.
Defined.

Lemma span_cons_decomposition x : module_span (fun y => y \in v :: s) x ->
    exists a : R, exists y : V,
      module_span (fun z => z \in s) y /\ a *: v + y = x.
Proof.
apply: (@span_least R V _ cons_decomposition).
move=> y; rewrite in_cons => /orP [/eqP ->|hy].
- exists 1, 0; split; first exact: span_zero.
  by rewrite scale1r addr0.
- exists 0, y; split; first exact: span_generator hy.
  by rewrite scale0r add0r.
Qed.

Lemma span_cons_redundant : module_span (fun y => y \in s) v -> forall x,
    module_span (fun y => y \in v :: s) x -> module_span (fun y => y \in s) x.
Proof.
move=> hv; apply: (@span_least R V _ (span_subspace (fun y => y \in s))).
move=> y; rewrite in_cons => /orP [/eqP ->|hy] => //.
exact: span_generator hy.
Qed.

Lemma span_tail x : module_span (fun y => y \in s) x ->
    module_span (fun y => y \in v :: s) x.
Proof.
apply: span_mono=> y hy; by rewrite in_cons hy orbT.
Qed.

End SpanCons.

Section AdjoinVector.
Variable K : fieldType.
Variable V U : lmodType K.
Variable f : {linear U -> V}.
Variable v : V.

Definition adjoin_map_fun (z : (K^o * U)%type) : V := z.1 *: v + f z.2.

Lemma adjoin_map_linear : linear adjoin_map_fun.
Proof.
move=> a [b x] [c y].
rewrite /adjoin_map_fun /= linearP scalerDl !scalerDr !scalerA /=.
by rewrite addrACA.
Qed.

HB.instance Definition _ := GRing.isLinear.Build K (K^o * U)%type V
  _ adjoin_map_fun adjoin_map_linear.

Definition adjoin_map : {linear (K^o * U)%type -> V} := adjoin_map_fun.

Lemma adjoin_map_injective (N : module_subspace V)
    (hf : injective f) (himage : forall u, N (f u)) (hv : ~ N v) :
    injective adjoin_map.
Proof.
have hker : forall z, adjoin_map z = 0 -> z = 0.
  move=> [a u] h.
  have ha : a = 0.
    case: (eqVneq a 0) => // ha; exfalso.
    have hN : N (a *: v).
      have he : a *: v = - f u.
        apply/eqP; rewrite -addr_eq0; apply/eqP; exact h.
      rewrite he; exact: subspace_opp (himage u).
    have hn := @subspace_scale K V N a^-1 (a *: v) hN.
    rewrite scalerA (mulVf ha) scale1r in hn; exact: hv hn.
  have hu : u = 0.
    apply: hf; rewrite linear0.
    have h0 : a *: v + f u = 0 := h.
    by rewrite ha scale0r add0r in h0.
  by rewrite ha hu.
move=> x y hxy; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: hker; by rewrite linearB hxy subrr.
Qed.

End AdjoinVector.

Section FiniteModels.
Variable K : fieldType.
Variable V : lmodType K.

Definition zero_model_fun (_ : 'rV[K]_0) : V := 0.
Lemma zero_model_linear : linear zero_model_fun.
Proof. by move=> a x y; rewrite /zero_model_fun scaler0 addr0. Qed.
HB.instance Definition _ := GRing.isLinear.Build K 'rV[K]_0 V
  _ zero_model_fun zero_model_linear.

Theorem finite_span_linear_model (s : seq V) :
    exists U : vectType K, exists f : {linear U -> V},
      injective f /\ forall x,
        (exists u : U, f u = x) <-> module_span (fun y => y \in s) x.
Proof.
elim: s => [|v s [U [f [hf him]]]].
- exists [the vectType K of 'rV[K]_0], (zero_model_fun : {linear 'rV[K]_0 -> V}); split.
  + move=> x y _; apply/matrixP=> i [j hj]; exfalso; by move: hj; rewrite ltn0.
  + move=> x; split.
    * move=> [u <-]; exact: span_zero.
    * move=> hx; exists 0.
      have hz : x = 0.
        apply: (@span_least K V _ (subspace_zero_space V)) _ hx.
        by move=> y; rewrite in_nil.
      exact: esym hz.
- case: (pselect (module_span (fun y => y \in s) v)) => hv.
  + exists U, f; split=> // x; split.
    * move=> hx; apply: span_tail; exact: (him x).1 hx.
    * move=> hx; apply: (him x).2; exact: (@span_cons_redundant K V v s hv x hx).
  + exists [the vectType K of (K^o * U)%type], (adjoin_map f v); split.
    * apply: (@adjoin_map_injective K V U f v (span_subspace (fun y => y \in s)))=> //.
      move=> u; apply: (him (f u)).1; by exists u.
    * move=> x; split.
      -- move=> [[a u] <-].
         apply: span_add.
         ++ apply: span_scale; apply: span_generator; by rewrite in_cons eqxx.
         ++ apply: span_tail; apply: (him (f u)).1; by exists u.
      -- move/span_cons_decomposition=> [a [y [hy <-]]].
         have [u <-] := (him y).2 hy; by exists (a,u).
Qed.

Theorem finitely_generated_linear_model : module_finitely_generated V ->
    exists U : vectType K, exists f : {linear U -> V}, bijective f.
Proof.
move=> [s hs]; have [U [f [hf him]]] := finite_span_linear_model s.
exists U, f.
have hsurj : forall x, exists u : U, f u = x.
  move=> x; exact: (him x).2 (hs x).
pose g x := proj1_sig (cid (hsurj x)).
have gK : cancel g f := fun x => proj2_sig (cid (hsurj x)).
exists g => // u; apply: hf; exact: gK.
Qed.

End FiniteModels.

Section FiniteDimensionalPackaging.
Variable K : fieldType.
Variable V : lmodType K.
Variable hfg : module_finitely_generated V.

Definition chosen_finite_model : vectType K :=
  proj1_sig (cid (finitely_generated_linear_model hfg)).

Definition chosen_model_map : {linear chosen_finite_model -> V} :=
  proj1_sig (cid (proj2_sig (cid (finitely_generated_linear_model hfg)))).

Lemma chosen_model_bijective : bijective chosen_model_map.
Proof. exact (proj2_sig (cid (proj2_sig (cid (finitely_generated_linear_model hfg))))). Qed.

Lemma chosen_model_inverse_exists : exists g : V -> chosen_finite_model,
    cancel chosen_model_map g /\ cancel g chosen_model_map.
Proof. have [g hg gh] := chosen_model_bijective; exists g; by split. Qed.

Definition chosen_model_inverse : V -> chosen_finite_model :=
  proj1_sig (cid chosen_model_inverse_exists).

Lemma chosen_model_inverseK : cancel chosen_model_inverse chosen_model_map.
Proof. exact (proj2 (proj2_sig (cid chosen_model_inverse_exists))). Qed.

Lemma chosen_model_mapK : cancel chosen_model_map chosen_model_inverse.
Proof. exact (proj1 (proj2_sig (cid chosen_model_inverse_exists))). Qed.

Lemma chosen_model_inverse_linear : linear chosen_model_inverse.
Proof. exact: can2_linear chosen_model_mapK chosen_model_inverseK. Qed.

HB.instance Definition _ := GRing.isLinear.Build K V chosen_finite_model
  _ chosen_model_inverse chosen_model_inverse_linear.

Definition chosen_model_coordinates : chosen_finite_model -> 'rV[K]_(dim chosen_finite_model) :=
  v2r (@vector_subdef K chosen_finite_model).

HB.instance Definition _ := GRing.isSemilinear.Build K chosen_finite_model
  'rV[K]_(dim chosen_finite_model) _ chosen_model_coordinates
  (v2r_semilinear (@vector_subdef K chosen_finite_model)).

Definition finite_coordinates x := chosen_model_coordinates (chosen_model_inverse x).

Lemma finite_coordinates_linear : linear finite_coordinates.
Proof. by move=> a x y; rewrite /finite_coordinates !linearP. Qed.

Lemma finite_coordinates_bijective : bijective finite_coordinates.
Proof.
have [g fg gf] := v2r_bijective (@vector_subdef K chosen_finite_model).
exists (fun x => chosen_model_map (g x)) => x.
- rewrite /finite_coordinates; change
    (chosen_model_map (g (v2r (@vector_subdef K chosen_finite_model) (chosen_model_inverse x))) = x).
  by rewrite fg chosen_model_inverseK.
- rewrite /finite_coordinates chosen_model_mapK; exact: gf.
Qed.

Definition finite_dimension_axiom : Vector.axiom (dim chosen_finite_model) V.
Proof. exists finite_coordinates; [exact: finite_coordinates_linear | exact: finite_coordinates_bijective]. Defined.

(** The original carrier and module operations are retained literally. *)
Definition finitely_generated_vect : vectType K :=
  HB.pack V (Lmodule_hasFinDim.Build K V finite_dimension_axiom).

Lemma finitely_generated_vect_same_carrier : (finitely_generated_vect : Type) = V.
Proof. reflexivity. Qed.

Lemma finitely_generated_vect_same_scale (a : K) (x : V) :
    (a *: (x : finitely_generated_vect) : finitely_generated_vect) = a *: x.
Proof. reflexivity. Qed.

End FiniteDimensionalPackaging.












