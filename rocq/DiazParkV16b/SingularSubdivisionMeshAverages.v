(** Quantitative estimates for actual finite averages over nested sets. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals.
From DiazParkV16b Require Import SingularSubdivisionMeshAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import DPSingularSubdivisionMeshAffine.
Local Open Scope ring_scope.

Module DPSingularSubdivisionMeshAverages.
Section Averages.
Variable Real : realType.
Variable I : finType.

Definition mesh_average (s : {set I}) (f : I -> Real) : Real :=
  (#|s|%:R)^-1 * \sum_(i in s) f i.

Lemma mesh_average_sub_const (s : {set I}) (hs : (0 < #|s|)%N)
    (f : I -> Real) c :
  mesh_average s f - c = (#|s|%:R)^-1 * \sum_(i in s) (f i - c).
Proof.
have hc : (#|s|%:R : Real) != 0 by rewrite pnatr_eq0; exact: lt0n_neq0 hs.
by rewrite sumrB sumr_const -(mulr_natl c #|s|) mulrBr /mesh_average mulrA mulVf // mul1r.
Qed.

Lemma mesh_average_sub_const_bound (s : {set I}) (hs : (0 < #|s|)%N)
    (f : I -> Real) c D (h : forall i, i \in s -> `|f i - c| <= D) :
  `|mesh_average s f - c| <= D.
Proof.
rewrite (mesh_average_sub_const hs) mulr_sumr.
have h0 : 0 <= (#|s|%:R : Real)^-1 by rewrite invr_ge0; exact: ler0n.
have hc : (#|s|%:R : Real) != 0 by rewrite pnatr_eq0; exact: lt0n_neq0 hs.
have hb := @weighted_sum_norm_bound Real I (mem s) (fun _ => (#|s|%:R)^-1)
  (fun i => f i - c) D (fun _ _ => h0) h.
by rewrite sumr_const -(mulr_natr ((#|s|%:R : Real)^-1) #|s|) mulVf // mul1r in hb.
Qed.

Lemma sum_mesh_average_centered (s : {set I}) (hs : (0 < #|s|)%N)
    (f : I -> Real) : \sum_(i in s) (mesh_average s f - f i) = 0.
Proof.
have hc : (#|s|%:R : Real) != 0 by rewrite pnatr_eq0; exact: lt0n_neq0 hs.
by rewrite sumrB sumr_const -(mulr_natl (mesh_average s f) #|s|)
  /mesh_average mulrA mulfV // mul1r subrr.
Qed.

Lemma mesh_average_sub_average (s t : {set I}) (hs : (0 < #|s|)%N)
    (hst : s \subset t) (f : I -> Real) :
  mesh_average s f - mesh_average t f =
    (#|t|%:R)^-1 * \sum_(j in t :\: s) (mesh_average s f - f j).
Proof.
have ht : (0 < #|t|)%N := leq_trans hs (subset_leq_card hst).
have hc : (#|t|%:R : Real) != 0 by rewrite pnatr_eq0; exact: lt0n_neq0 ht.
have he : t :&: s = s.
  apply/setP => i; rewrite inE; apply/andP/idP.
  - by case.
  - move=> hi; split=> //; exact (fintype.subsetP hst i hi).
have hz := sum_mesh_average_centered hs f.
have hsum : \sum_(j in t) (mesh_average s f - f j) =
    (\sum_(j in t :&: s) (mesh_average s f - f j)) +
      \sum_(j in t :\: s) (mesh_average s f - f j) := big_setID s _.
rewrite he hz add0r in hsum.
by rewrite -hsum sumrB sumr_const -(mulr_natl (mesh_average s f) #|t|)
  mulrBr mulrA mulVf // mul1r.
Qed.

Lemma mesh_average_nested_bound (s t : {set I}) (hs : (0 < #|s|)%N)
    (hst : s \subset t) (f : I -> Real) D
    (h : forall i, i \in s -> forall j, j \in t -> `|f i - f j| <= D) :
  `|mesh_average s f - mesh_average t f| <=
    (#|t|%:R)^-1 * (#|t :\: s|%:R) * D.
Proof.
rewrite (mesh_average_sub_average hs hst) mulr_sumr.
have h0 : 0 <= (#|t|%:R : Real)^-1 by rewrite invr_ge0; exact: ler0n.
have hb : forall j, j \in t :\: s -> `|mesh_average s f - f j| <= D.
  move=> j hj; apply: (mesh_average_sub_const_bound hs) => i hi.
  apply: (h i hi); move: hj; by rewrite inE => /andP[_].
have he := @weighted_sum_norm_bound Real I (mem (t :\: s))
  (fun _ => (#|t|%:R)^-1) (fun j => mesh_average s f - f j) D (fun _ _ => h0) hb.
by rewrite sumr_const -(mulr_natr ((#|t|%:R : Real)^-1) #|t :\: s|) in he.
Qed.

End Averages.
End DPSingularSubdivisionMeshAverages.
