Lemma ex1: forall A, ~~~A -> ~A.
Proof.
    unfold not.
    intros.
    apply H.
    intros.
    apply H1, H0.
Qed.

Lemma ex2: forall A B, A \/ B -> ~(~A /\ ~B).
Proof.
    unfold not.
    intros.
    destruct H, H0.
    apply H0.
    assumption.
    apply H1.
    assumption.
Qed.

Lemma ex3: forall T (P: T -> Prop), 
    (~exists x, P x) -> forall x, ~P x.
Proof.
    unfold not.
    intros.
    destruct H.
    exists x.
    assumption.
Qed.
