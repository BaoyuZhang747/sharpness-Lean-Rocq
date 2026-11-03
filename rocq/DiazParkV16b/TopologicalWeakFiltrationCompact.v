(** Compact subsets of a countable exhaustive weak filtration lie in one stage.
    The T1 and genuine final-topology hypotheses are explicit intermediate data. *)
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical topology.
From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module DPTopologicalWeakFiltrationCompact.

Lemma finite_subset_monotone_cover (X : choiceType) (A : nat -> set X)
  (hm : forall n m, (n <= m)%N -> A n `<=` A m)
  (hc : forall x, exists n, A n x) (S : set X) (hS : finite_set S) :
  exists n, S `<=` A n.
Proof.
have hseq : forall s : seq X, exists n, forall x, x \in s -> A n x.
  elim=> [|x s [n hn]].
  - exists 0%N; by move=> x; rewrite in_nil.
  - have [m hx] := hc x. exists (maxn n m).
    move=> y; rewrite in_cons => /orP[/eqP ->|hy].
    + exact: (hm m (maxn n m) (leq_maxr n m) x hx).
    + exact: (hm n (maxn n m) (leq_maxl n m) y (hn y hy)).
have [n hn] := hseq (enum_fset (fset_set S)).
exists n => x hx; apply hn.
by rewrite (in_fset_set hS) inE.
Qed.

Section Pointed.
Variable X : topologicalType.
Variable x0 : X.
Let pointed_space : Type := X.
HB.instance Definition _ := Topological.on pointed_space.
HB.instance Definition _ := isPointed.Build pointed_space x0.

Lemma compact_all_subsets_closed_finite (Q : set pointed_space)
  (hQ : compact Q) (hclosed : forall B : set pointed_space, B `<=` Q -> closed B) : finite_set Q.
Proof.
pose U (x : X) := ~` (Q `\` [set x]).
have hopen : forall x, Q x -> open (U x).
  move=> x _; rewrite /U openC; apply hclosed; by move=> y [hy _].
have hcover : Q `<=` cover Q U.
  move=> x hx; exists x; first exact hx.
  move=> [_ hxx]; apply hxx; reflexivity.
rewrite compact_cover in hQ.
have [D hD hcov] := hQ X Q U hopen hcover.
apply: (@sub_finite_set X Q [set` D]); last exact: finite_fset.
move=> x hx; have [y hy hU] := hcov x hx.
have e : x = y.
  apply: contrapT => hxy. apply hU; split; first exact hx.
  exact hxy.
by rewrite e.
Qed.

End Pointed.

Lemma escaping_sequence_intersection_finite (X : choiceType) (A : nat -> set X)
  (hm : forall n m, (n <= m)%N -> A n `<=` A m)
  (z : nat -> X) (hz : forall n, ~ A n (z n))
  (B : set X) (hB : B `<=` range z) n : finite_set (B `&` A n).
Proof.
apply: (@sub_finite_set X (B `&` A n) (z @` `I_n)).
  move=> x [hx hxn]; have [k _ e] := hB x hx.
  exists k; last exact e.
  apply/negP => hkn; have hnk : (n <= k)%N by rewrite leqNgt; apply/negP.
  apply (hz k); apply: (hm n k hnk); by rewrite e.
exact: finite_image (finite_II n).
Qed.

(** The compactness argument itself uses only the weak-closed-set consequence;
    the next theorem derives this consequence from actual stage maps. *)
Lemma compact_monotone_weak_filtration (X : topologicalType) (A : nat -> set X)
  (hm : forall n m, (n <= m)%N -> A n `<=` A m)
  (hc : forall x, exists n, A n x)
  (hw : forall B : set X, (forall n, finite_set (B `&` A n)) -> closed B)
  (K : set X) (hK : compact K) : exists n, K `<=` A n.
Proof.
apply: contrapT => hnone.
have hbad n : exists x, K x /\ ~ A n x.
  apply: contrapT => hn; apply hnone; exists n => x hx.
  apply: contrapT => hnx; apply hn; by exists x.
pose z n := projT1 (cid (hbad n)).
have hzK n : K (z n) by exact: (projT2 (cid (hbad n))).1.
have hzA n : ~ A n (z n) by exact: (projT2 (cid (hbad n))).2.
pose Q := range z.
have hclosed : forall B : set X, B `<=` Q -> closed B.
  move=> B hB; apply hw => n.
  exact: (escaping_sequence_intersection_finite hm hzA hB n).
have hQK : Q `<=` K by move=> x [n _ <-]; exact (hzK n).
have hQclosed : closed Q by apply hclosed.
have hQcompact : compact Q := subclosed_compact hQclosed hK hQK.
have hQfinite : finite_set Q :=
  @compact_all_subsets_closed_finite X (z 0%N) Q hQcompact hclosed.
have [n hn] := finite_subset_monotone_cover hm hc hQfinite.
apply (hzA n); apply hn; by exists n.
Qed.

Lemma compact_in_weak_filtration (X : topologicalType)
  (Y : nat -> topologicalType) (f : forall n, Y n -> X)
  (hf : forall n, continuous (f n))
  (hm : forall n m, (n <= m)%N -> range (f n) `<=` range (f m))
  (hc : forall x, exists n, range (f n) x)
  (hT1 : accessible_space X)
  (hfinal : forall B : set X, (forall n, closed (f n @^-1` B)) -> closed B)
  (K : set X) (hK : compact K) : exists n, K `<=` range (f n).
Proof.
apply: (compact_monotone_weak_filtration hm hc _ hK).
move=> B hB; apply hfinal => n.
have he : f n @^-1` B = f n @^-1` (B `&` range (f n)).
  apply/predeqP => y; split=> [hy|[hy _]]; last exact hy.
  split=> //; by exists y.
rewrite he; apply: preimage_closed.
- by move=> x hx; exact: (hf n x).
- exact: (accessible_finite_set_closed.1 hT1 _ (hB n)).
Qed.

End DPTopologicalWeakFiltrationCompact.
