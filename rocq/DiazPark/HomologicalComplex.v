From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Nonnegative cochain complexes of arbitrary MathComp modules.  No term is
    assumed finite, finite dimensional, free, or finitely generated.  This file
    does not define higher limits: the comparison with derived limits remains
    a separate obligation of the port. *)
Module DiazParkHomological.

Section Complexes.
Variable R : pzRingType.

Record cochain_complex := CochainComplex {
  cochain_term : nat -> lmodType R;
  cochain_d : forall n, {linear cochain_term n -> cochain_term n.+1};
  cochain_d2 : forall n x, cochain_d n.+1 (cochain_d n x) = 0
}.

Definition cocycle (C : cochain_complex) n (x : cochain_term C n) : Prop :=
  cochain_d C n x = 0.

Arguments cocycle _ _ _ : clear implicits.

Definition coboundary (C : cochain_complex) n : cochain_term C n -> Prop :=
  match n as k return cochain_term C k -> Prop with
  | 0%N => fun x => x = 0
  | k.+1 => fun x => exists y, cochain_d C k y = x
  end.

Arguments coboundary _ _ _ : clear implicits.

Lemma coboundary_cocycle (C : cochain_complex) n (x : cochain_term C n) :
  coboundary C n x -> cocycle C n x.
Proof.
case: n x => [|n] x /=.
- by move=> ->; rewrite /cocycle linear0.
- by move=> [y <-]; exact: cochain_d2.
Qed.

Definition positive_acyclic (C : cochain_complex) : Prop :=
  forall n (x : cochain_term C n.+1),
    cocycle C n.+1 x -> coboundary C n.+1 x.

Definition all_degree_acyclic (C : cochain_complex) : Prop :=
  forall n (x : cochain_term C n), cocycle C n x -> coboundary C n x.

Record cochain_map (C D : cochain_complex) := CochainMap {
  cochain_map_at : forall n, {linear cochain_term C n -> cochain_term D n};
  cochain_map_commutes : forall n x,
    cochain_d D n (cochain_map_at n x) =
      cochain_map_at n.+1 (cochain_d C n x)
}.

Lemma cochain_map_cocycle (C D : cochain_complex) (f : cochain_map C D)
    n (x : cochain_term C n) :
  cocycle C n x -> cocycle D n (cochain_map_at f n x).
Proof. by move=> hx; rewrite /cocycle cochain_map_commutes hx linear0. Qed.

Lemma cochain_map_coboundary (C D : cochain_complex) (f : cochain_map C D)
    n (x : cochain_term C n) :
  coboundary C n x -> coboundary D n (cochain_map_at f n x).
Proof.
case: n x => [|n] x /=.
- by move=> ->; rewrite linear0.
- move=> [y <-]; exists (cochain_map_at f n y).
  exact: cochain_map_commutes.
Qed.

(** A contracting homotopy is supplied as actual linear maps.  Its degree-zero
    identity is explicit, so all-degree vanishing does not silently omit H^0. *)
Record contracting_homotopy (C : cochain_complex) := ContractingHomotopy {
  contraction : forall n, {linear cochain_term C n.+1 -> cochain_term C n};
  contraction_zero : forall x,
    contraction 0%N (cochain_d C 0%N x) = x;
  contraction_succ : forall n x,
    cochain_d C n (contraction n x) +
      contraction n.+1 (cochain_d C n.+1 x) = x
}.

Arguments contraction_succ {C} h n x : rename.

Lemma contraction_acyclic (C : cochain_complex) (h : contracting_homotopy C) :
  all_degree_acyclic C.
Proof.
move=> [|n] x hx.
- have hc := contraction_zero h x.
  by rewrite /cocycle in hx; rewrite hx linear0 in hc; exact: esym hc.
- exists (contraction h n x).
  have hc := contraction_succ h n x.
  by rewrite /cocycle in hx; rewrite hx linear0 addr0 in hc.
Qed.

(** Exactness is stated pointwise, using actual module elements.  No quotient
    construction, finite-dimensional rank theorem, or choice of bases is used. *)
Record degreewise_short_exact (A B C : cochain_complex)
    (f : cochain_map A B) (g : cochain_map B C) := DegreewiseShortExact {
  short_exact_injective : forall n, injective (cochain_map_at f n);
  short_exact_composite : forall n x,
    cochain_map_at g n (cochain_map_at f n x) = 0;
  short_exact_kernel : forall n y,
    cochain_map_at g n y = 0 -> exists x, cochain_map_at f n x = y;
  short_exact_surjective : forall n z, exists y, cochain_map_at g n y = z
}.

Arguments short_exact_injective {A B C f g} s n : rename.
Arguments short_exact_composite {A B C f g} s n x : rename.
Arguments short_exact_kernel {A B C f g} s n y _ : rename.
Arguments short_exact_surjective {A B C f g} s n z : rename.

(** Elementwise proof of the short-exact extension step in the manuscript's
    bar-complex lemma.  It works for arbitrary module values over any ring. *)
Theorem positive_acyclic_extension (A B C : cochain_complex)
    (f : cochain_map A B) (g : cochain_map B C)
    (s : degreewise_short_exact f g) :
  positive_acyclic A -> positive_acyclic C -> positive_acyclic B.
Proof.
move=> hA hC n z hz.
have hgz : cocycle C n.+1 (cochain_map_at g n.+1 z) :=
  cochain_map_cocycle g hz.
have [c hc] := hC n _ hgz.
have [b hb] := short_exact_surjective s n c.
have hu : cochain_map_at g n.+1 (z - cochain_d B n b) = 0.
  by rewrite linearB -cochain_map_commutes hb hc subrr.
have [a ha] := short_exact_kernel s n.+1 _ hu.
have hda : cocycle A n.+1 a.
  apply: (short_exact_injective s n.+2).
  rewrite linear0 -cochain_map_commutes ha linearB.
  by rewrite /cocycle in hz; rewrite hz cochain_d2 subrr.
have [a0 ha0] := hA n a hda.
exists (cochain_map_at f n a0 + b).
by rewrite linearD cochain_map_commutes ha0 ha subrK.
Qed.

Theorem all_degree_acyclic_extension (A B C : cochain_complex)
    (f : cochain_map A B) (g : cochain_map B C)
    (s : degreewise_short_exact f g) :
  all_degree_acyclic A -> all_degree_acyclic C -> all_degree_acyclic B.
Proof.
move=> hA hC [|n] z hz.
- have hgz := cochain_map_cocycle g hz.
  have hgz0 := hC 0%N _ hgz.
  have [a ha] := short_exact_kernel s 0%N _ hgz0.
  have hda : cocycle A 0%N a.
    apply: (short_exact_injective s 1%N).
    by rewrite linear0 -cochain_map_commutes ha.
  have ha0 := hA 0%N a hda.
  by rewrite /coboundary -ha ha0 linear0.
- have hApos : positive_acyclic A by move=> k; exact: hA k.+1.
  have hCpos : positive_acyclic C by move=> k; exact: hC k.+1.
  exact: (@positive_acyclic_extension A B C f g s hApos hCpos n z hz).
Qed.

(** This is the cocycle-level relation that a future cohomology quotient must
    identify.  Giving it a name here does not assert construction of a quotient
    module or its comparison with Ext. *)
Definition cohomologous (C : cochain_complex) n (x y : cochain_term C n) : Prop :=
  coboundary C n (x - y).

Arguments cohomologous _ _ _ _ : clear implicits.

Record cochain_homotopy (C D : cochain_complex) (f g : cochain_map C D) :=
  CochainHomotopy {
    homotopy_map : forall n, {linear cochain_term C n.+1 -> cochain_term D n};
    homotopy_zero : forall x,
      cochain_map_at f 0%N x - cochain_map_at g 0%N x =
        homotopy_map 0%N (cochain_d C 0%N x);
    homotopy_succ : forall n x,
      cochain_map_at f n.+1 x - cochain_map_at g n.+1 x =
        cochain_d D n (homotopy_map n x) +
          homotopy_map n.+1 (cochain_d C n.+1 x)
  }.

Arguments homotopy_succ {C D f g} h n x : rename.

Lemma homotopy_cohomologous (C D : cochain_complex) (f g : cochain_map C D)
    (h : cochain_homotopy f g) n (x : cochain_term C n) :
  cocycle C n x ->
    cohomologous D n (cochain_map_at f n x) (cochain_map_at g n x).
Proof.
case: n x => [|n] x hx.
- by rewrite /cohomologous /coboundary (homotopy_zero h x) hx linear0.
- exists (homotopy_map h n x).
  have hh := homotopy_succ h n x.
  by rewrite hx linear0 addr0 in hh; exact: esym hh.
Qed.

End Complexes.

Arguments cocycle {R} C n x.
Arguments coboundary {R} C n x.
Arguments cohomologous {R} C n x y.
End DiazParkHomological.
