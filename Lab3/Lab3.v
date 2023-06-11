Theorem double_denial: forall A, ~~A -> A.
Proof.
intros.

Lemma ex1: forall A, ~~~A -> ~A.
Proof.
intros.
destruct H.
assert(h: A -> ~~A).
intros.


assumption.


Qed.

Lemma ex2: forall A B, A \/ B -> ~(~A /\ ~B).
Proof.
auto.
Qed.

Lemma ex3: forall T (P: T -> Prop),
(~exists x, P x) -> forall x, ~P x.
Proof.
auto.
Qed.