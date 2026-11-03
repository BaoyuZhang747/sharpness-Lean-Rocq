From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation.
From DiazPark Require Import FusionCentralizerMaps FusionCentralizer.
Import DPFusion DPFusionSubgroup DPFusionCentralizer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerExtension.
Section Domain.
Variable S : finGroupType.
Variable E : {group S}.
Hypothesis abE : abelian E.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Variables P Q : {group T}.
Variable f : DPFusion.map P Q.
Variable fhat : DPFusion.map (joint P) (joint Q).
Hypothesis hext : forall x : T, x \in P -> fhat (val x) = val (f x).
Hypothesis hfix : {in E, fhat =1 id}.

Lemma joint_product (R : {group T}) : (joint (E := E) R : {set S}) = ambient R * E.
Proof. exact: cent_joinEl (ambient_sub R). Qed.

Lemma joint_normalizer (R : {group T}) (s : T) :
  s \in 'N(R) -> val s \in 'N(joint R).
Proof.
move=> Ns; apply/normP.
rewrite /joint /= conjYg.
have eR : ambient R :^ (val s) = ambient R.
  apply/setP=> x; apply/idP/idP.
  - case/imsetP=> y /morphimP[z _ Rz ->] ->.
    change (val (z ^ s) \in ambient R); apply: ambient_mem.
    by rewrite memJ_norm.
  - case/morphimP=> z _ Rz ->.
    apply/imsetP; exists (val (z ^ s^-1)).
    + apply: ambient_mem; by rewrite memJ_norm ?groupV.
    + change (val z = val ((z ^ s^-1) ^ s)); by rewrite conjgKV.
have Ne : val s \in 'N(E) := subsetP (cent_sub E) _ (valP s).
by rewrite eR (normP Ne).
Qed.

Lemma centralizer_conjugation (s : T) e : e \in E -> e ^ (val s) = e.
Proof. by move=> Ee; rewrite conjgE -(centP (valP s) e Ee) mulKg. Qed.

Lemma extension_domain_ambient :
  ambient (DPFusionSaturation.extension_domain f) \subset
    DPFusionSaturation.extension_domain fhat.
Proof.
apply/subsetP=> _ /morphimP[s _ /setIdP[Ns /exists_inP[t Nt /forall_inP hst]] ->].
apply/setIdP; split; first exact: joint_normalizer Ns.
apply/exists_inP; exists (val t); first exact: joint_normalizer Nt.
apply/forall_inP=> x; rewrite joint_product => /mulsgP[y e Py Ee ->]; apply/eqP.
have /morphimP[z _ Pz ez] := Py; change (y = val z) in ez; subst y.
have Pzs : z ^ s \in P by rewrite memJ_norm.
have vP : val z \in joint P := subsetP (joint_left P) _ (ambient_mem Pz).
have vPs : val (z ^ s) \in joint P := subsetP (joint_left P) _ (ambient_mem Pzs).
have eP : e \in joint P := subsetP (joint_right P) _ Ee.
change (fhat ((val z * e) ^ (val s)) = (fhat (val z * e)) ^ (val t)).
rewrite conjMg (centralizer_conjugation s Ee).
change (fhat (val (z ^ s) * e) = (fhat (val z * e)) ^ (val t)).
rewrite (DPFusion.map_mul fhat vPs eP) (DPFusion.map_mul fhat vP eP)
  (hext Pzs) (hext Pz) (hfix Ee) conjMg (centralizer_conjugation t Ee).
have h := eqP (hst z Pz).
exact: (congr1 (fun w : T => val w * e) h).
Qed.

Lemma extension_domain_E : E \subset DPFusionSaturation.extension_domain fhat.
Proof.
apply/subsetP=> e Ee; apply/setIdP; split.
- exact: subsetP (normG (joint P)) _ (subsetP (joint_right P) e Ee).
- apply/exists_inP; exists e.
  + exact: subsetP (normG (joint Q)) _ (subsetP (joint_right Q) e Ee).
  + apply/forall_inP=> x Px; apply/eqP.
    have h := morphJ (DPFusion.map_morphism fhat) Px (subsetP (joint_right P) e Ee).
    change (fhat (x ^ e) = (fhat x) ^ (fhat e)) in h.
    rewrite (hfix Ee) in h.
    exact h.
Qed.

Lemma extension_domain_joint :
  joint (DPFusionSaturation.extension_domain f) \subset
    DPFusionSaturation.extension_domain fhat.
Proof. by rewrite /joint join_subG extension_domain_ambient extension_domain_E. Qed.

End Domain.
End DPFusionCentralizerExtension.
