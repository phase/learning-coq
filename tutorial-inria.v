(* 
  Following the inria.fr Coq Tutorial
  https://coq.inria.fr/tutorial/
*)

(* `Check` shows the Type of an expression. *)
Check 0. (* 0 : nat *)
Check nat. (* nat : Set *)

(* Sections structure cide by limiting parameters,
   hypotheses, & definitions. *)
Section Declaration.
  (* let n be a natural number *)
  Variable n : nat.

  (*  let n be a positive natrual number *)
  Hypotheses Pos_n : (gt n 0).
  Check gt. (* gt : nat -> nat -> Prop *)
  Check gt n 0. (* n > 0 : Prop *)

  Definition one := (S 0).
  Definition two : nat := S one.
  Definition three := S two : nat.
  Definition double (m : nat) := plus m m.
  (* using a free variable *)
  Definition add_n (m : nat) := plus m n.

  Check (forall m : nat, gt m 0).
End Declaration.

Section Minimal_Logic.
  Variables A B C : Prop.
  Check (A -> B).
  (* manually create a goal *)
  Goal (A -> B -> C) -> (A -> B) -> A -> C.
    intros.
    (* apply a hypothesis *)
    apply H.
      apply H1.

      apply H0.
      (* use what we already know *)
      assumption.
  Qed.

  (* redo above *)
  Lemma distr_impl : (A -> B -> C) -> (A -> B) -> A -> C.
    intros.
    apply H; [ assumption | apply H0; assumption ].
  Qed.

  Lemma distr_impl__again : (A -> B -> C) -> (A -> B) -> A -> C.
    auto.
  Qed.
End Minimal_Logic.

Section Propositional_Calculus.
  Lemma and_commutative : (forall A B : Prop, A /\ B -> B /\ A).
    intros.
    (* use conjunctive hypothesis H to break into components *)
    elim H.
    (* splits the conjunctive goal into two subgoals *)
    (* split is an abbreviation for apply conj *)
    split.
    exact H1.
    exact H0.
  Qed.

  Lemma or_communtative : (forall A B : Prop, A \/ B -> B \/ A).
    intros.
    elim H.
    auto.
    (* H is no longer needed! *)
    clear H.
    auto.
  Qed.

  Lemma or_communtative__again : (forall A B : Prop, A \/ B -> B \/ A).
    intros.
    destruct H.
      (* H : A*)
      right.
      exact H.

      (* H : B *)
      left.
      exact H.
  Qed.
  
  Lemma or_communtative__3 : (forall A B : Prop, A \/ B -> B \/ A).
    (* "propsitional tautologies" *)
    tauto.
  Qed.
  Print or_communtative__3.

  Lemma NNPeirce : (forall A B : Prop, ~ ~ (((A -> B) -> A) -> A)).
    tauto.
  Qed.

  Require Import Classical.
  Check NNPP.
  Lemma Peirce : (forall A B : Prop, ((A -> B) -> A) -> A).
    intros.
    apply NNPP.
    tauto.
  Qed.
End Propositional_Calculus.

Section Club.
(*
Here is one more example of propositional reasoning, 
in the shape of a Scottish puzzle. 
A private club has the following rules:

    Every non-scottish member wears red socks
    Every member wears a kilt or doesn’t wear red socks
    The married members don’t go out on Sunday
    A member goes out on Sunday if and only if he is Scottish
    Every member who wears a kilt is Scottish and married
    Every scottish member wears a kilt
*)

  Variables Scottish RedSocks WearKilt Married GoOutSunday : Prop.
  Hypothesis rule1 : ~ Scottish -> RedSocks.
  Hypothesis rule2 : WearKilt \/ ~ RedSocks.
  Hypothesis rule3 : Married -> ~ GoOutSunday.
  Hypothesis rule4 : GoOutSunday <-> Scottish.
  Hypothesis rule5 : WearKilt -> Scottish /\ Married.
  Hypothesis rule6 : Scottish -> WearKilt.

  (* The rules are so strict, no one can join *)
  Lemma NoMember : False.
    tauto.
  Qed.

  Check NoMember.
End Club.

Section Predicate_Calculus.
  Variable D : Set.
  Variable R : D -> D -> Prop.
  Hypothesis R_symmetric : forall x y : D, R x y -> R y x.
  Hypothesis R_transitive :
          forall x y z : D, R x y -> R y z -> R x z.

  Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
    intros.
    elim H.
    intros.
    apply R_transitive with x0.
    exact H0.
    apply R_symmetric.
    exact H0.
  Qed.

  Variable P : D -> Prop.
  Variable d : D.
  Lemma weird : (forall x : D, P x) -> exists a, P a.
    intro UnivP.
    exists d.
    trivial.
  Qed.
End Predicate_Calculus.
