(** Finite leading-column elimination in the actual downward total. *)
From Coq Require Import Arith Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazParkV16b Require Import ChainComplex FirstQuadrantChainBicomplex FirstQuadrantChainTotal FirstQuadrantChainTotalMaps FirstQuadrantChainTotalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPFirstQuadrantChain DPFirstQuadrantChainTotal DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainSupport.
Local Open Scope ring_scope.
Module DPFirstQuadrantChainTotalAcyclic.
Section Signs.
Variable R : pzRingType.
Variable V : lmodType R.
Lemma sign_scale_twice p (x : V) : (-1:R)^+p *: ((-1:R)^+p *: x)=x.
Proof.
elim: p=> [|p ih]; first by rewrite expr0 !scale1r.
by rewrite exprS mulN1r !scaleNr scalerN opprK ih.
Qed.
Lemma sign_scale_zero p (x : V) : (-1:R)^+p *: x=0 -> x=0.
Proof. move=> h; rewrite -(sign_scale_twice p x) h scaler0; reflexivity. Qed.
End Signs.
Section Acyclic.
Variable R : pzRingType.
Variable K : bicomplex R.
Lemma leading_cycle n (a : total_term K n) : @cycle R (total_complex K) n a ->
 forall p q (h : (p+q)%coq_nat=n), supported_before a p.+1 ->
 @cycle R (vertical_complex K p) q (a p q h).
Proof.
move=> hc p [|q] h hs; first exact I.
case: n a hc h hs=> [|n] a hc h hs; first by exfalso; lia.
have h0 : (p+q)%coq_nat=n by lia.
have he := congr1 (fun z : total_term K n => z p q h0) hc.
change (horizontal K p q (a p.+1 q (horizontal_input h0))+
 (-1:R)^+p *: vertical K p q (a p q.+1 (vertical_input h0))=0) in he.
have hp : (p.+1<=p.+1)%coq_nat by lia.
rewrite (hs _ _ _ hp) linear0 add0r in he.
have hh : vertical_input h0=h by apply Prop_irrelevance.
rewrite hh in he; exact: sign_scale_zero he.
Qed.
Lemma supported_step n (a : total_term K n) p q (h : (p+q)%coq_nat=n) :
 supported_before a p.+1 -> a p q h=0 -> supported_before a p.
Proof.
move=> hs hx r t ht hr.
case (Nat.eq_dec p r)=> [e|e].
- destruct e.
  have et : q=t by lia.
  destruct et.
  have eh : ht=h by apply Prop_irrelevance.
  by rewrite eh.
- apply hs; lia.
Qed.
Lemma total_d_include_vertical p q n (h : (p+q)%coq_nat=n) (y : bicomplex_term K p q.+1) :
 @total_d R K n (total_include (vertical_input h) ((-1:R)^+p *: y)) p q h = vertical K p q y.
Proof.
change (horizontal K p q (@total_include R K p q.+1 n.+1 (vertical_input h) ((-1:R)^+p *: y) p.+1 q (horizontal_input h))+
 (-1:R)^+p *: vertical K p q (@total_include R K p q.+1 n.+1 (vertical_input h) ((-1:R)^+p *: y) p q.+1 (vertical_input h)) = vertical K p q y).
have hp : p<>p.+1 by lia.
rewrite (@total_include_other R K p q.+1 n.+1 (vertical_input h) ((-1:R)^+p *: y) p.+1 q (horizontal_input h) hp) total_include_same linear0 add0r linearZ.
exact: sign_scale_twice.
Qed.
Lemma cycle_subtract_boundary n (a : total_term K n) (b : total_term K n.+1) :
 @cycle R (total_complex K) n a -> @cycle R (total_complex K) n (a-total_d b).
Proof.
case: n a b=> [|n] a b hc; first exact I.
change (total_d (a-total_d b)=0).
rewrite linearB.
change (total_d a-total_d (total_d b)=0).
change (total_d a=0) in hc.
by rewrite total_d_squared hc subrr.
Qed.
Variable hcolumns : forall p, acyclic (vertical_complex K p).
Lemma total_cycle_boundary_supported n k : forall (a : total_term K n),
 @cycle R (total_complex K) n a -> supported_before a k -> @boundary R (total_complex K) n a.
Proof.
elim: k=> [|k ih] a hc hs.
- have ha := supported_before_zero hs; subst a.
  exists 0; exact: linear0.
- case (le_gt_dec k n)=> hkn.
  + pose q := (n-k)%coq_nat.
    have h : (k+q)%coq_nat=n by rewrite /q; lia.
    have hl := leading_cycle hc h hs.
    have [y hy] := @hcolumns k q (a k q h) hl.
    pose b := total_include (vertical_input h) ((-1:R)^+k *: y).
    have hb : supported_before b k.+1 := total_include_supported _ _.
    have hdb := total_d_supported hb.
    have hsame : @total_d R K n b k q h=a k q h by rewrite /b total_d_include_vertical; exact hy.
    have he : supported_before (a-total_d b) k.+1.
      move=> p t ht hp; change (a p t ht-@total_d R K n b p t ht=0).
      by rewrite (hs _ _ _ hp) (hdb _ _ _ hp) subrr.
    have he0 : (a-total_d b) k q h=0 by change (a k q h-@total_d R K n b k q h=0); rewrite hsame subrr.
    have hes := @supported_step n (a-total_d b) k q h he he0.
    have [z hz] := ih (a-total_d b) (@cycle_subtract_boundary n a b hc) hes.
    exists (z+b); change (total_d (z+b)=a).
    rewrite linearD hz; exact: subrK.
  + apply ih; first exact hc.
    move=> p q h hp; exfalso; lia.
Qed.
Theorem total_acyclic : acyclic (total_complex K).
Proof. move=> n a ha; exact: total_cycle_boundary_supported ha (supported_diagonal a). Qed.
End Acyclic.
End DPFirstQuadrantChainTotalAcyclic.
