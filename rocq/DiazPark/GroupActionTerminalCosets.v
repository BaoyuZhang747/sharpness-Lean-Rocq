(** The actual unique transporter coset from a fixed point to its chosen
    orbit representative, whose target group is the full stabilizer. *)
From mathcomp Require Import all_boot all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import GroupOrbitCategory GroupActionOrbitRepresentatives.
Import DPGroupOrbit DPLeftAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPActionTerminal.
Section Action.
Variable G : finGroupType.
Variable X : finType.
Variable act : G -> X -> X.
Hypothesis act_one : forall x, act 1 x = x.
Hypothesis act_mul : forall g h x, act (g*h) x = act g (act h x).
Local Notation Stab x := (DPLeftAction.stabilizer act_one act_mul x).
Definition fixed (H : {group G}) x := forall h, h \in H -> act h x = x.

Lemma related_action (H K : {group G}) (f g : transporter H K) y :
    fixed K y -> DPGroupOrbit.related f g -> act (val f) y = act (val g) y.
Proof.
  move=> hy /eqP he.
  have hf : val f \in val g *: K by rewrite -he; exact (lcoset_refl _ _).
  move/lcosetP: hf => [k hk ->]. by rewrite act_mul (hy k hk).
Qed.
Definition coset_action (H K : {group G}) (f : orbit_hom H K) y := act (val (repr f)) y.
Lemma coset_action_class (H K : {group G}) (f : transporter H K) y :
    fixed K y -> coset_action (DPGroupOrbit.orbit_class f) y = act (val f) y.
Proof. move=> hy. exact (related_action hy (representative_related f)). Qed.

Lemma fixed_stabilizer y : fixed (Stab y) y.
Proof. move=> h hh. exact (elimT (stabilizerP act_one act_mul y h) hh). Qed.

Lemma fixed_transporter (H : {group G}) x y g :
    fixed H x -> act g y = x -> H :^ g \subset Stab y.
Proof.
  move=> hx he. apply/subsetP=> h.
  rewrite mem_conjg => hh. apply/stabilizerP.
  apply (@act_injective G X act act_one act_mul g).
  have hf := hx (h ^ g^-1) hh.
  rewrite -he in hf.
  rewrite conjgE invgK -!act_mul !mulgA mulgKV in hf.
  by rewrite -act_mul.
Qed.

Lemma coset_action_injective (H : {group G}) y :
    injective (fun f : orbit_hom H (Stab y) => coset_action f y).
Proof.
  move=> f g he. rewrite /coset_action in he.
  rewrite -(reprK f) -(reprK g). apply/DPGroupOrbit.orbit_class_eq/eqP/lcoset_eqP/lcosetP.
  exists ((val (repr g))^-1 * val (repr f)).
  - apply/stabilizerP. rewrite act_mul he.
    exact (act_cancel act_one act_mul (val (repr g)) y).
  - by rewrite mulgA mulgV mul1g.
Qed.

Variable p : nat.
Variable T : {group G}.
Hypothesis sylT : p.-Sylow([set: G]) T.
Hypothesis stabilizers_pgroup : forall x, p.-group (Stab x).
Local Notation Index := (DPLeftAction.orbit_index act_one act_mul).
Local Notation rep := (DPLeftAction.representative sylT stabilizers_pgroup).
Local Notation cls := (DPLeftAction.orbit_class act_one act_mul).

Definition terminal_coset (H : {group G}) x (hx : fixed H x) :
    {i : Index & {f : orbit_hom H (Stab (rep i)) | coset_action f (rep i) == x}}.
Proof.
  refine (existT _ (cls x) _).
  have hex : exists f : transporter H (Stab (rep (cls x))), act (val f) (rep (cls x)) == x.
    have /existsP[g /eqP hg] := class_representative_related sylT stabilizers_pgroup x.
    exists (Sub g (fixed_transporter hx hg)). apply/eqP; exact hg.
  have [f /eqP hf] := sigW hex.
  exists (DPGroupOrbit.orbit_class f).
  apply/eqP.
  rewrite coset_action_class; first exact hf. exact: fixed_stabilizer.
Defined.

Lemma terminal_index (H : {group G}) x i
    (f : orbit_hom H (Stab (rep i))) : coset_action f (rep i) = x -> cls x = i.
Proof.
  move=> <-. rewrite /coset_action orbit_class_translate.
  exact: representative_class.
Qed.

Theorem terminal_coset_unique (H : {group G}) x
    (t u : {i : Index & {f : orbit_hom H (Stab (rep i)) | coset_action f (rep i) == x}}) : t = u.
Proof.
  case: t => i f. case: u => j g.
  have hij : i = j := eq_trans (esym (terminal_index (eqP (valP f)))) (terminal_index (eqP (valP g))).
  destruct hij. f_equal. apply val_inj.
  apply (@coset_action_injective H (rep i)). exact (eq_trans (eqP (valP f)) (esym (eqP (valP g)))).
Qed.

End Action.
End DPActionTerminal.
