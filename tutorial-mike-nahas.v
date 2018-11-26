(*
  This is a test document filled with exercises from
  https://coq.inria.fr/tutorial-nahas
*)

Theorem my_first_proof__again__again : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
  intros A.
  intros B.
  intros proof_of_A.
  intros A_implies_B.
  pose (proof_of_B := A_implies_B proof_of_A).
  exact proof_of_B.
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros.
  refine (H0 _).
    exact H.
Qed.

Theorem backward_large : (forall A B C : Prop, A -> (A -> B) -> (B -> C) -> C).
Proof.
  intros.
  refine (H1 _).
  refine (H0 _).
  exact H.
Qed.

Theorem backward_huge : (forall A B C : Prop, 
                         A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
  intros.
  refine (H1 _ _).
    exact H.
    refine (H0 _).
      exact H.
Qed.

Theorem forward_huge : (forall A B C : Prop, 
                        A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
  intros.
  pose (proof_of_B := H0 H).
  pose (proof_of_C := H1 H proof_of_B).
  exact proof_of_C.
Qed.

Theorem True_can_be_proven : True.
Proof.
  exact I.
Qed.

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven__again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem absurd : forall A C : Prop, A -> ~A -> C.
Proof.
  intros.
  unfold not in H0.
  pose (proof_of_False := H0 H).
  case proof_of_False.
Qed.

Require Import Bool.

Theorem true_is_True: Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  (* these next two aren't actually needed!*)
  unfold not.
  simpl.
  exact False_cannot_be_proven.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros.
  case a.
    (*simpl.*)
    exact I.
    (*simpl.*)
    exact I.
Qed.

Theorem thm_eqb_a_t: (forall a : bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
    simpl.
    intros proof_of_True.
    exact I.

    simpl.
    intros proof_of_False.
    case proof_of_False.
Qed.

Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
  exact proof_of_A_or_B.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
    exact proof_of_B.
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
    intros proof_of_A.
    refine (or_intror _).
    exact proof_of_A.

    intros proof_of_B.
    refine (or_introl _).
    exact proof_of_B.
Qed.

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros.
  refine (conj _ _).
    exact H.
    exact H0.
Qed.

Theorem and_commutes : (forall A B : Prop, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros proof_of_A_and_B.
  case proof_of_A_and_B.
   intros proof_of_A proof_of_B.
   refine (conj _ _).
     exact proof_of_B.
     exact proof_of_A.
Qed.

Theorem and_communtes__again : (forall A B : Prop, A /\ B -> B /\ A).
Proof.
  intros.
  destruct H as [proof_of_A proof_of_B].
  refine (conj _ _).
    exact proof_of_B.
    exact proof_of_A.
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros.
    case a, b.
      simpl.
      exact (or_introl I).

      simpl.
      exact (or_introl I).

      simpl.
      exact (or_intror I).

      simpl in H.
      refine (or_introl _).
      simpl.
      case H.
    intros.
    case a,b.
      exact I.
      exact I.
      exact I.
      case H.
        intros A.
        simpl in A.
        case A.

        intros B.
        simpl in B.
        case B.
Qed.

Theorem andb_is_and : (forall a b, 
                       Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      simpl.
      exact (conj I I).

      simpl in H.
      case H.

      simpl in H.
      case H.

      simpl in H.
      case H.
    intros H.
    case a, b.
      simpl.
      exact I.

      simpl in H.
      destruct H as [A B].
      case B.

      simpl in H.
      destruct H as [A B].
      case A.

      simpl in H.
      destruct H as [A B].
      case A.
Qed.

(* !a <-> !A where a : bool, A : Prop *)
Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros.
  unfold iff.
  case a.
    (* a is true *)
    simpl.
    refine (conj _ _).
      (* False -> ~True *)
      intros.
      unfold not.
      case H.

      (* ~True -> False *)
      unfold not.
      intros.
      case H.
      exact I.
    (* a is false *)
    simpl.
    refine (conj _ _).
      (* True -> ~False*)
      unfold not.
      intros.
      case H0.

      (* ~False -> True *)
      unfold not.
      intros.
      exact I.
Qed.

Definition basic_predicate := (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    simpl.
    exact I.
Qed.

Theorem thm_exists_basics__again : (exists a, Is_true (andb a true)).
Proof.
  pose (witness := true).
  refine (ex_intro _ witness _).
  simpl.
  exact I.
Qed.

Theorem thm_forall_exists : (forall b, (exists a, Is_true (eqb a b))).
Proof.
  intros.
  case b.
    (* b = true *)
    refine (ex_intro _ true _).
      simpl.
      exact I.
    (* b = false *)
    refine (ex_intro _ false _).
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists__simple : (forall b, (exists a, Is_true (eqb a b))).
Proof.
  intros.
  refine (ex_intro _ b _).
  exact (eqb_a_a b).
Qed.

Theorem forall_exists : (forall P : Set -> Prop, 
                        (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros.
  unfold not in H.
  unfold not.
  intros exists_set_px.
  destruct exists_set_px as [exists_set exists_px].
  pose (not_Pwitness := H exists_set exists_px).
  case not_Pwitness.
Qed.

Theorem forall_exists__book : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  intros forall_x_not_Px.
  unfold not.
  intros exists_x_Px.
  destruct exists_x_Px as [witness proof_of_Pwitness].
  pose (not_Pwitness := forall_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (proof_of_False := not_Pwitness proof_of_Pwitness).
  case proof_of_False.
Qed.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.

Theorem them_eq_trans : (forall x y z : Set, x = y -> y = z -> x = z).
Proof.
  intros.
  destruct H as [].
  destruct H0 as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros.
  rewrite H.
  rewrite H0.
  exact (eq_refl z).
Qed.

Theorem thm_eq_trans__again2 : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros.
  rewrite H.
  rewrite <-H0.
  exact (eq_refl y).
Qed.

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
  intros.
  case a, b.
    simpl.
    exact (eq_refl true).

    simpl.
    exact (eq_refl false).

    simpl.
    exact (eq_refl false).

    simpl.
    exact (eq_refl false).
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
  intros.
  unfold not.
  case a.
    simpl.
    discriminate.
    simpl.
    discriminate.
Qed.

Theorem neq_nega__book: (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.
    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.

    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.
Qed.

(* Peano Arithmetic *)

Theorem plus_2_3 : (2 + 3 = 5).
  simpl.
  exact (eq_refl 5).
Qed.

Theorem plus_2_3_long : (S (S O)) + (S (S (S O))) = (S (S (S (S (S O))))).
Proof.
  simpl.
  exact (eq_refl 5).
Qed.

Theorem plus_O_n : (forall n, O + n = n).
Proof.
  intros n.
  simpl.
  exact (eq_refl n).
Qed.

Theorem plus_n_O : (forall n, n + O = n).
Proof.
  intros n.
  elim n.
    (* base case *)
    simpl.
    exact (eq_refl _).

    (* inductive case *)
    intros.
    simpl.
    rewrite H.
    exact (eq_refl _).
Qed.

Theorem plus_symmetric : (forall n m, n + m = m + n).
Proof.
  intros.
  elim n.
    elim m.
      simpl.
      exact (eq_refl _).

      intros.
      simpl.
      rewrite <- H.
      simpl.
      exact (eq_refl _).
    intros.
    simpl.
    rewrite H.
    elim m.
      simpl.
      exact (eq_refl _).

      intros.
      simpl.
      rewrite H0.
      exact (eq_refl _).
Qed.

Require Import List.

(* Adding an element to a list increases its length by 1 *)
Theorem cons_adds_one_to_length :
    (forall A : Type,
    (forall (x : A) (lst : list A),
     length (x :: lst) = (S (length lst)))).
Proof.
  intros.
  simpl.
  exact (eq_refl _).
Qed.

Definition hd (A : Type) (default : A) (l : list A) :=
match l with
| nil => default
| x :: _ => x
end.

(* currying the above function with 2 parameters*)
Definition hd_for_nat_lists := hd nat 0.
(* Compute hd_for_nat_lists (5 :: 4 :: nil). *)
(* Compute hd_for_nat_lists (nil). *)

Theorem correctness_of_hd :
    (forall A : Type,
    (forall (default : A) (x : A) (l : list A),
    (hd A default nil) = default /\ (hd A default (x :: l) = x))).
Proof.
  intros.
  simpl.
  refine (conj _ _).
    exact (eq_refl _).
    exact (eq_refl _).
Qed.

(* `: option A` can be inferred *)
Definition hd_error (A : Type) (l : list A) : option A :=
match l with
| nil => None
| x :: _ => Some x
end.
(* Compute hd_error nat nil.
Compute hd_error nat (5 :: 4 :: nil). *)

Theorem correctness_of_hd_error :
    (forall A : Type,
    (forall (x : A) (l : list A),
    (hd_error A nil) = None /\ (hd_error A (x :: l)) = Some x)).
Proof.
  intros.
  simpl.
  refine (conj _ _).
    exact (eq_refl _).
    exact (eq_refl _).
Qed.

(* some crazy shit?!?! *)
(* pass a proof that hte list is not nil *)
Definition hd_never_fail (A : Type) (lst : list A) (safety_proof : lst <> nil)
  : A
:=
  (match lst as b return (lst = b -> A) with
    | nil => (fun foo : lst = nil =>
                   match (safety_proof foo) return A with
                   end
                )
    | x :: _ => (fun foo : lst = x :: _ =>
                   x
                )
  end) eq_refl.

Theorem correctness_of_hd_never_fail :
   (forall A:Type,
   (forall (x : A) (rest : list A),
   (exists safety_proof : ((x :: rest) <> nil),
      (hd_never_fail A (x :: rest) safety_proof) = x))).
Proof.
  intros.
  assert (witness : ((x :: rest) <> nil)).
    unfold not.
    intros.
    discriminate H.
  refine (ex_intro _ witness _).
    simpl.
    exact (eq_refl _).
Qed.

Definition tl (A : Type) (l:list A) :=
  match l with
    | nil => nil
    | a :: m => m
  end.

Theorem hd_tl :
   (forall A:Type,
   (forall (default : A) (x : A) (lst : list A),
   (hd A default (x::lst)) :: (tl A (x::lst)) = (x :: lst))).
Proof.
  intros.
  simpl.
  exact (eq_refl _).
Qed.

(* exercises *)

Theorem app_nil_l : (forall A : Type, (forall l : list A, nil ++ l = l)).
Proof.
  intros.
  simpl.
  exact (eq_refl _).
Qed.

Theorem app_nil_r : (forall A:Type, (forall l:list A, forall l:list A, l ++ nil = l)).
Proof.
  intros.
  simpl.
  elim l0.
    simpl.
    exact (eq_refl _).
  intros.
  simpl.
  rewrite H.
  exact (eq_refl _).
Qed.

Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros.
  simpl.
  exact (eq_refl _).
Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  elim l.
    simpl.
    exact (eq_refl _).
  intros.
  simpl.
  rewrite H.
  exact (eq_refl _).
Qed.

Theorem app_cons_not_nil : forall A (x y:list A) (a:A), nil <> x ++ a :: y.
Proof.
  intros.
  unfold not.
  elim x.
    simpl.
    discriminate.

    intros.
    simpl in H0.
    discriminate H0.
Qed.

