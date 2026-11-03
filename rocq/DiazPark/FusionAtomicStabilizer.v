From mathcomp Require Import all_ssreflect all_fingroup quotient pgroup nilpotent.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionSaturationImage
  FusionConjugacy FusionAutomorphisms FusionOrbit FusionOuterAutomorphisms
  FusionOuterOrbit FusionOuterAction.
Import DPFusion DPFusionAutomorphisms DPFusionOrbit DPFusionOuter DPFusionOuterAction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicStabilizer.
Section Stabilizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables Q P : {group S}.
Variable raw : DPFusionSystem.arrow F Q P.
Local Notation f := (val raw).
Local Notation L := (DPFusion.image f).
Local Notation N := 'N_P(L)%G.
Local Notation A := (DPFusionSaturation.aut_group F Q).

Lemma inverse_image : DPFusion.image (DPFusion.inverse f) = Q.
Proof.
apply: val_inj; change (DPFusion.map_morphism (DPFusion.inverse f) @* L = Q).
by rewrite /DPFusion.inverse DPFusion.of_morphism_image im_invm.
Qed.

Definition normalizer_aut s := aut_transport (DPFusion.inverse f) (conj_aut L s).

Lemma normalizer_aut_allowed s : s \in N -> normalizer_aut s \in A.
Proof.
move=> /setIP[_ Ns].
have aA : conj_aut L s \in DPFusionSaturation.aut_group F L.
  apply: (subsetP (DPFusionSaturation.ambient_aut_sub F L)).
  by apply/morphimP; exists s.
have h := aut_transport_allowed (DPFusionSystem.inverse_closed (valP raw)) aA.
by rewrite inverse_image in h.
Qed.

Lemma normalizer_autE s : s \in N -> {in Q, forall x, f (normalizer_aut s x) = (f x)^s}.
Proof.
move=> /setIP[Ps Ns] x Qx.
have Lfx : f x \in L := DPFusion.image_mem f Qx.
have Ac : conj_aut L s \in Aut L := Aut_aut _ _.
have h := aut_transportE (DPFusion.inverse f) Ac Lfx.
rewrite DPFusion.inverse_cancel // norm_conj_autE // in h.
have Lfxs : (f x)^s \in L by rewrite memJ_norm.
rewrite /normalizer_aut h DPFusion.inverse_cancel_right //.
Qed.

Lemma normalizer_aut_morphic : {in N &, {morph normalizer_aut : s t / s*t}}.
Proof.
move=> s t /setIP[Ps Ns] /setIP[Pt Nt].
rewrite /normalizer_aut /aut_transport (morphM (conj_aut L) Ns Nt).
exact: (morphM (Aut_isom (DPFusion.map_injm (DPFusion.inverse f)) (subxx L))
  (Aut_aut _ _) (Aut_aut _ _)).
Qed.

Canonical normalizer_aut_morphism := Morphism normalizer_aut_morphic.

Definition normalizer_outer s := coset (inner Q) (normalizer_aut s).

Lemma normalizer_outer_morphic : {in N &, {morph normalizer_outer : s t / s*t}}.
Proof.
move=> s t Ns Nt; rewrite /normalizer_outer (normalizer_aut_morphic Ns Nt).
exact: (morphM (coset (inner Q))
  (subsetP (normal_norm (inner_normal F Q)) _ (normalizer_aut_allowed Ns))
  (subsetP (normal_norm (inner_normal F Q)) _ (normalizer_aut_allowed Nt))).
Qed.

Canonical normalizer_outer_morphism := Morphism normalizer_outer_morphic.

Lemma normalizer_outer_stabilizes s : s \in N ->
  normalizer_outer s \in stabilizer (orbit_class raw).
Proof.
move=> Ns; apply/(stabilizer_coset_iff raw (normalizer_aut_allowed Ns)).
exists s; split; first exact: (setIP Ns).1.
exact: normalizer_autE Ns.
Qed.

Lemma stabilizer_witness_normalizes a (Aa : a \in A) n :
  {in Q, forall x, f (a x) = (f x)^n} -> n \in 'N(L).
Proof.
move=> he; rewrite inE; apply/subsetP=> y /imsetP[z /morphimP[x Qx _ ->] ->].
change ((f x)^n \in L).
rewrite -(he x Qx); apply: DPFusion.image_mem.
exact: (Aut_closed (subsetP (DPFusionSaturation.aut_group_sub F Q) _ Aa) Qx).
Qed.

Lemma normalizer_aut_eq a (Aa : a \in A) n (Nn : n \in N) :
  {in Q, forall x, f (a x) = (f x)^n} -> normalizer_aut n = a.
Proof.
move=> he.
have Ar := subsetP (DPFusionSaturation.aut_group_sub F Q) _ (normalizer_aut_allowed Nn).
have Aa' := subsetP (DPFusionSaturation.aut_group_sub F Q) _ Aa.
apply: (eq_Aut Ar Aa')=> x Qx.
apply: (DPFusion.map_injective (f := f) (Aut_closed Ar Qx) (Aut_closed Aa' Qx)).
by rewrite normalizer_autE // he.
Qed.

Lemma normalizer_outer_image :
  normalizer_outer_morphism @* N = stabilizer (orbit_class raw).
Proof.
apply/setP=> g; apply/idP/idP.
- move=> /morphimP[n Nn _ ->]; exact: normalizer_outer_stabilizes Nn.
- move=> Gf.
  have Gg := subsetP (stabilizer_sub (orbit_class raw)) g Gf.
  have [Aa ea] := representative_spec Gg.
  have hfix : coset (inner Q) (representative F g) \in stabilizer (orbit_class raw).
    by rewrite ea.
  have [n [Pn hn]] := proj1 (stabilizer_coset_iff raw Aa) hfix.
  have Nn : n \in N.
    apply/setIP; split; first exact Pn.
    exact: (stabilizer_witness_normalizes Aa hn).
  have en := normalizer_aut_eq Aa Nn hn.
  apply/morphimP; exists n=> //.
  change (g = coset (inner Q) (normalizer_aut n)).
  by rewrite en ea.
Qed.

Lemma normalizer_aut_image_element x : x \in Q ->
  normalizer_aut (f x) = conj_aut Q x.
Proof.
move=> Qx.
have Lfx := DPFusion.image_mem f Qx.
have Nfx : f x \in N.
  by apply/setIP; split; [exact: DPFusion.map_into Qx | exact: subsetP (normG L) _ Lfx].
have Aa : conj_aut Q x \in A.
  apply: (subsetP (inner_sub F Q)); exact: mem_morphim (subsetP (normG Q) x Qx) Qx.
apply: (normalizer_aut_eq Aa Nfx).
move=> y Qy; rewrite conj_autE //.
exact: (morphJ (DPFusion.map_morphism f) Qy Qx).
Qed.

Lemma image_sub_kernel : L \subset 'ker normalizer_outer_morphism.
Proof.
apply/subsetP=> _ /morphimP[x Qx _ ->].
change (f x \in 'ker normalizer_outer_morphism).
apply/morphpreP; split.
- apply/setIP; split; first exact: DPFusion.map_into Qx.
  exact: subsetP (normG L) _ (DPFusion.image_mem f Qx).
- apply/set1P; change (coset (inner Q) (normalizer_aut (f x)) = 1).
  rewrite normalizer_aut_image_element //.
  apply: coset_id; exact: mem_morphim (subsetP (normG Q) x Qx) Qx.
Qed.

Lemma normalizer_outer_kernel (cL : 'C(L) \subset L) :
  'ker normalizer_outer_morphism = L.
Proof.
apply/eqP; rewrite eqEsubset image_sub_kernel andbT.
apply/subsetP=> s /morphpreP[Ns /set1P hs].
have Aa := normalizer_aut_allowed Ns.
have Ni := subsetP (normal_norm (inner_normal F Q)) _ Aa.
have Ia : normalizer_aut s \in inner Q := coset_idr Ni hs.
have /morphimP[q _ Qq eqr] := Ia.
have Lfq := DPFusion.image_mem f Qq.
have eqconj : {in L, forall y, y^s = y^(f q)}.
  move=> y /morphimP[x Qx _ ->].
  change ((f x)^s = (f x)^(f q)).
  rewrite -(normalizer_autE Ns Qx) eqr conj_autE //.
  exact: (morphJ (DPFusion.map_morphism f) Qx Qq).
have hc : s * (f q)^-1 \in 'C(L).
  apply/centP=> y Ly; apply/esym/commgP/conjg_fixP.
  by rewrite conjgM eqconj // conjgK.
have hL := groupM (subsetP cL _ hc) Lfq.
by rewrite mulgKV in hL.
Qed.

Lemma stabilizer_pgroup (p : nat) : p.-group P -> p.-group (stabilizer (orbit_class raw)).
Proof.
move=> pP; rewrite -normalizer_outer_image.
apply: morphim_pgroup; exact: pgroupS (subsetIl P 'N(L)) pP.
Qed.

Lemma stabilizer_isog (cL : 'C(L) \subset L) :
  (N / L) \isog stabilizer (orbit_class raw).
Proof.
have h := first_isog normalizer_outer_morphism.
by rewrite normalizer_outer_kernel // normalizer_outer_image in h.
Qed.
End Stabilizer.
End DPFusionAtomicStabilizer.






