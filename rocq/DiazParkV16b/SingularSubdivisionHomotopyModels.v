(** Filling the actual subdivision defect on the standard simplex models. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category BarFreeModule.
From DiazParkV16b Require Import ChainComplex TopologicalCategory TopologicalSimplexBasic
  SingularSet SimplicialChains SimplicialChainsMaps SingularCohomology SingularChainMapsLaws
  SingularContractibleChains SingularModelOperators SingularSubdivisionOperators SingularSubdivisionBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPTopological DPTopologicalSimplex
  DPSingularSet DPSingularCohomology DPSingularChainMapsLaws DPSingularContractibleChains
  DPSingularModelOperators DPSingularSubdivision DPSingularSubdivisionBoundary DPSimplicialChainMaps.
Local Open Scope ring_scope.

Module DPSingularSubdivisionHomotopyModels.
Section Models.
Variable Real : realType.
Variable R : pzRingType.
Let C X := singular_chains Real R X.
Definition model_chain n := chain_term (C (simplex_space Real n)) n.+1.
Definition model_identity n := free_basis R (identity_simplex Real n).

Lemma model_operator_zero n m (X : topologicalType) (x : chain_term (C X) n) :
  model_operator (0 : chain_term (C (simplex_space Real n)) m) X x = 0.
Proof.
rewrite /model_operator /free_lift; apply: big1_seq => s _.
by rewrite linear0 scaler0.
Qed.

Definition successor_equation n (a : model_chain n) (b : model_chain n.+1) : Prop :=
  forall (X : topologicalType) (x : chain_term (C X) n.+1),
    chain_d (C X) n.+1 (model_operator b X x) +
      model_operator a X (chain_d (C X) n x) = subdivision_at Real R X n.+1 x - x.

Definition model_defect n (a : model_chain n) : chain_term (C (simplex_space Real n.+1)) n.+1 :=
  subdivision_at Real R (simplex_space Real n.+1) n.+1 (model_identity n.+1) -
    model_identity n.+1 - model_operator a (simplex_space Real n.+1)
      (chain_d (C (simplex_space Real n.+1)) n (model_identity n.+1)).

Lemma model_filling_equation n (a : model_chain n) (b : model_chain n.+1)
    (hb : chain_d (C (simplex_space Real n.+1)) n.+1 b = model_defect a) :
  successor_equation a b.
Proof.
move=> X x.
apply (free_lift_ext
  (g := ((chain_d (C X) n.+1 \o model_operator b X) \+
    (model_operator a X \o chain_d (C X) n) : {linear _ -> _}))
  (h := ((subdivision_at Real R X n.+1 : {linear _ -> _}) \-
    (idfun : {linear _ -> _}) : {linear _ -> _}))).
move=> s.
change (chain_d (C X) n.+1 (model_operator b X (free_basis R s)) +
  model_operator a X (chain_d (C X) n (free_basis R s)) =
  subdivision_at Real R X n.+1 (free_basis R s) - free_basis R s).
rewrite model_operator_basis chain_map_commutes hb /model_defect !linearB.
have hsd := @subdivision_naturality Real R (simplex_space Real n.+1) X s n.+1 (model_identity n.+1).
have hm := @model_operator_naturality Real R n n.+1 a (simplex_space Real n.+1) X s
  (chain_d (C (simplex_space Real n.+1)) n (model_identity n.+1)).
change (chain_map_at (singular_chain_map Real R s) n.+1
  (subdivision_at Real R (simplex_space Real n.+1) n.+1 (model_identity n.+1)) =
  subdivision_at Real R X n.+1
    (chain_map_at (singular_chain_map Real R s) n.+1 (model_identity n.+1))) in hsd.
rewrite hsd /model_identity singular_generator_model hm -chain_map_commutes /model_identity singular_generator_model.
by rewrite subrK.
Qed.

Inductive model_tower : forall n, model_chain n -> Type :=
| model_tower_zero : model_tower (0 : model_chain 0)
| model_tower_succ : forall n (a : model_chain n), model_tower a ->
    forall b : model_chain n.+1, successor_equation a b -> model_tower b.

Lemma tower_cycle_equation n (a : model_chain n) (T : model_tower a)
    (X : topologicalType) (x : chain_term (C X) n) :
  @cycle R (C X) n x -> chain_d (C X) n (model_operator a X x) =
    subdivision_at Real R X n x - x.
Proof.
move: X x; case: T => [|k aa TT bb hb] X x hx.
- rewrite model_operator_zero linear0 subdivision_degree_zero subrr; reflexivity.
- have e := hb X x; move: e.
  change (chain_d (C X) k x = 0) in hx.
  rewrite hx linear0 addr0; exact: id.
Qed.

Lemma model_defect_cycle n (a : model_chain n) (T : model_tower a) :
  @cycle R (C (simplex_space Real n.+1)) n.+1 (model_defect a).
Proof.
change (chain_d (C (simplex_space Real n.+1)) n (model_defect a) = 0).
rewrite /model_defect !linearB.
have hc : @cycle R (C (simplex_space Real n.+1)) n
    (chain_d (C (simplex_space Real n.+1)) n (model_identity n.+1)).
  apply: (@boundary_cycle R (C (simplex_space Real n.+1)) n).
  exists (model_identity n.+1); reflexivity.
rewrite (tower_cycle_equation T hc).
change (@DPSimplicialChains.boundary R (singular_set Real (simplex_space Real n.+1)) n
  (subdivision_at Real R (simplex_space Real n.+1) n.+1 (model_identity n.+1)) -
  chain_d (C (simplex_space Real n.+1)) n (model_identity n.+1) -
  (subdivision_at Real R (simplex_space Real n.+1) n
    (chain_d (C (simplex_space Real n.+1)) n (model_identity n.+1)) -
   chain_d (C (simplex_space Real n.+1)) n (model_identity n.+1)) = 0).
by rewrite subdivision_boundary subrr.
Qed.

Definition next_model n (a : model_chain n) (T : model_tower a) :
    { b : model_chain n.+1 | successor_equation a b }.
Proof.
have h := @simplex_positive_exact Real R n.+1 n (model_defect a) (model_defect_cycle T).
have [b hb] := constructive_indefinite_description h.
exists b; exact: model_filling_equation hb.
Defined.

Fixpoint chosen_model (n : nat) : { a : model_chain n & model_tower a } :=
  match n with
  | 0%N => existT _ 0 model_tower_zero
  | k.+1 =>
      match chosen_model k with
      | existT a T =>
          match next_model T with
          | exist b hb => existT _ b (@model_tower_succ k a T b hb)
          end
      end
  end.

Definition universal_homotopy_chain n : model_chain n := projT1 (chosen_model n).

Lemma universal_homotopy_chain_zero : universal_homotopy_chain 0 = 0.
Proof. reflexivity. Qed.

Theorem universal_homotopy_chain_succ n :
  successor_equation (universal_homotopy_chain n) (universal_homotopy_chain n.+1).
Proof.
rewrite /universal_homotopy_chain /=.
case: (chosen_model n) => a T /=.
case: (next_model T) => b hb /=; exact hb.
Qed.

End Models.
End DPSingularSubdivisionHomotopyModels.

