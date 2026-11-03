From DiazPark Require Import Category.
Set Implicit Arguments.
Lemma iso_conjugate_identity {C : category} {A B : C} (e : isomorphism A B)
    (f : hom C A A)
    (h : compose (compose (iso_inv e) f) (iso_hom e) = identity B) : f = identity A.
Proof.
  pose proof (f_equal (fun k : hom C B B => compose (compose (iso_hom e) k) (iso_inv e)) h) as H.
  cbn beta in H.
  repeat rewrite <- compose_assoc in H.
  rewrite iso_hom_inv, compose_id_left,
    compose_assoc, iso_hom_inv, !compose_id_right, iso_hom_inv in H.
  exact H.
Qed.
