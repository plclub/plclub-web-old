(* ============================================================================ 
                  Extra libarary for  POPLmark challenges 
                             Jevgenijs Sallinens 
                              June/November 2005
   ============================================================================ *)

(* ============================================================================ *)
(**
Some definitions and results about  natural numbers,lists and types.
Some obvious results are given without proof as axioms, just to reduce space and
efforts.
*)
(* ============================================================================ *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import Bool.
Require Import List.
Require Import Arith.
Require Import tactics.
Opaque TRUE.

(* ============================================================================ *)
(**  * Natural Numbers *)
(* ============================================================================ *)

(** 
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
*)

(** Order relation for natural numbers. *)

Fixpoint nat_le (n m:nat) {struct n}:bool:=
  match n, m with
  | O, _       => true
  | S _, O     => false
  | S n1, S m1 => nat_le n1 m1
  end.

Infix "<==" := nat_le (at level 70, no associativity).

(** Equlaity of natural numbers. *)

Definition n_eq (n m :nat):= (n <== m) && (m <== n).

Infix "==" := n_eq (at level 70, no associativity).

Axiom n_eq_le: forall n m, n == m -> n <== m.

Axiom n_eq_refl: forall n, n == n.

Axiom n_eq_sym: forall n m, n == m -> m == n.

Axiom n_le_trans: forall m n k, m <== n -> n <== k -> m <== k.

Axiom n_eq_trans: forall n m k, n == m -> m == k -> n == k.

Axiom n_eq_1: forall x y, x == y -> x = y.

Axiom n_eq_2: forall x y, x == y -> y = x.

Axiom b_eq_add_S : forall n m, S n == S m -> n == m.

Axiom b_le_add_S: forall n m, S m <== S n -> m <==  n.

Axiom eq_S : forall n m, n == m -> S n == S m.

Axiom le_S: forall n m,  m <== n -> S m <== S n.

Axiom b_le_ge_eq: forall n n', n <== n' -> n' <== n -> n = n'.

Axiom not_le_S_n: forall n, S n <== n -> false.

Axiom not_S_O: forall n, S n == 0 -> false.

Axiom le_n_Sn: forall n, n <== S n.

Axiom le_pred_n: forall n, pred n <== n.

Axiom b_pred_Sn: forall n,  pred (S n) = n.

Axiom b_S_pred: forall n, (n <== O -> false) -> S (pred n) =n.

Axiom le_pred: forall n n',  n' <==  n -> pred n' <== pred n.

Axiom b_le_or_ge: forall n n', (S n' <== n -> false) -> n <== n'.

Axiom b_ge_or_le: forall n n', (n' <== n -> false) -> S n <== n'.

Axiom le_eq_O: forall n, n <== O -> n = O.

Axiom N_Decide: forall (x y:nat)(P:Prop), ((S x <== y) -> P) -> ((y <== x) -> P) -> P.

Axiom nat_le_leq:forall n m, n <== m -> n <= m.

Hint Resolve n_eq_le n_eq_refl n_eq_sym b_le_ge_eq b_ge_or_le le_n_Sn le_pred_n b_pred_Sn 
not_S_O not_le_S_n.
       


(** Two operations with natural numbers to introduce shiftings and substitutions. 
Also usefull to formulate results about lists concatenation *)

Definition S_Next (Y X:nat):= if (nat_le Y X) then S X else X.
Definition S_Pred (Y X:nat):= if (nat_le Y X) then Y else (pred Y).

Lemma S_Next_le:forall (Y X:nat), Y <== X -> S_Next Y X =  S X.
Proof.
intros Y X H;unfold S_Next.
apply Decide with (S X <== Y);intro;b_rewrite.
Qed.

Lemma S_Next_gt:forall (Y X:nat), S X <== Y -> S_Next Y X =  X.
Proof.
intros Y X H;unfold S_Next.
apply Decide with (Y <== X);intro;b_rewrite.
apply Contradiction;apply not_le_S_n with X.
apply n_le_trans with Y;auto.
Qed.

Lemma S_Pred_le:forall (Y X:nat), X <== Y -> (Y == X -> false) -> S (S_Pred Y X) = Y.
Proof.
intros Y X H1 H2;unfold S_Pred.
apply Decide with (Y <== X);intro;b_rewrite.
apply Contradiction;apply H2;rewrite b_le_ge_eq with Y X;auto.
apply b_S_pred.
intros;apply H.
apply n_le_trans with 0;auto.
Qed.


Lemma S_Pred_gt:forall (Y X:nat), S Y <== X -> S_Pred Y X =  Y.
Proof.
intros Y X H;unfold S_Pred.
cut (TRUE (Y <== X));intros.
b_rewrite;auto.
apply n_le_trans with (S Y);auto.
Qed.

(** Usefull lemmas for reasoning about lists concatenations and type shiftings. *)

Lemma S_Next_Pred: forall x x',
  (x == x' -> false)-> S_Next x' (S_Pred x x') =  x.
Proof.
intros n n' H;unfold S_Pred;unfold S_Next.
apply Decide with (n <== n');intro;b_rewrite.
apply Decide with (n' <== n);intro;b_rewrite.
apply Contradiction;apply H.
rewrite b_le_ge_eq with n n';auto.
apply Decide with (n' <== pred n);intro;b_rewrite.
apply b_S_pred.
intro;apply H0;apply n_le_trans with O;auto.
apply Contradiction;apply H.
rewrite b_le_ge_eq with n n';auto.
apply b_le_or_ge;auto .
intros;apply H1.
apply b_le_add_S;auto.
apply n_le_trans with n;auto.
rewrite b_S_pred;auto.
intro;apply H0;apply n_le_trans with O;auto.
apply b_le_or_ge;auto;intro;apply H0.
apply n_le_trans with (S n);auto.
Qed.


Lemma S_Pred_Next: forall x x',
  S_Pred (S_Next x' x) x' =  x.
intros n n';unfold S_Pred;unfold S_Next.
apply Decide with (n <== n');intro;b_rewrite.
apply Decide with (n' <== n);intro;b_rewrite.
apply Decide with (S n <== n');intro;b_rewrite.
apply Contradiction;apply not_le_S_n with n;auto.
apply n_le_trans with n';auto.
b_rewrite.
apply Decide with (n' <== n);intro;b_rewrite.
apply Decide with (S n <== n');intro;b_rewrite.
apply Contradiction;apply not_le_S_n with n;auto.
apply n_le_trans with n';auto.
apply Contradiction;apply H;auto.
apply b_le_or_ge.
intro;apply H0.
apply n_le_trans with (S n');auto.
Qed.


Lemma S_Next_S_S: forall n n', 
  S_Next (S n') (S n) = S (S_Next n' n).
Proof.
intros n n';unfold S_Next.
apply Decide with (S n' <== S n);intro;b_rewrite.
apply Decide with (n' <== n);intro.
rewrite  if_then_true;auto.
rewrite  if_then_false;auto.
apply Decide with (n' <== n);intro.
apply Contradiction;apply H.
apply le_S;auto.
rewrite  if_then_false;auto.
Qed.

Lemma S_Pred_S_S: forall n n', 
  S_Pred (S n') (S n) = S (S_Pred n' n).
Proof.
intros n n';unfold S_Pred.
apply Decide with (S n' <== S n);intro;b_rewrite.
apply Decide with (n' <== n);intro.
rewrite  if_then_true;auto.
rewrite  if_then_false;auto.
apply Decide with (n' <== n);intro.
apply Contradiction;apply H;apply le_S;auto.
rewrite  if_then_false;auto.
rewrite b_pred_Sn;auto.
rewrite b_S_pred;auto;intro;apply H0.
apply n_le_trans with O;auto.
Qed.

(* ============================================================================ *)
(** * Lists *)
(* ============================================================================ *)

Section Lists.
Variable A:Set.

Fixpoint len (e:list A){struct e}:nat:=
  match e  with
  | nil        => 0
  | T' :: e'   => S (len e')
  end.

(** Well-formed indices of lists. *)

Fixpoint wfi (e:list A) (X:nat) {struct e}:bool:=
  match e, X with
  | nil    , _   => false
  | T :: e',O    => true 
  | T :: e',S X' => wfi e' X' 
  end.

Lemma wfi_app_cons: forall e e0 T, wfi (e ++ T :: e0) (len e).
Proof.
induction e;simpl;intros;auto.
Qed.

Lemma wfi_app:  forall e X e0 T0,  
   wfi (e ++ e0) X ->  wfi (e ++ T0 :: e0) (S_Next (len e) X).
Proof.
induction e;induction X;simpl;auto.
rewrite S_Next_S_S;auto.
Qed.

Lemma wfi_app_1:  forall e X e0 T0,  
    wfi (e ++ T0 :: e0) (S_Next (len e) X)->wfi (e ++ e0) X.
Proof.
induction e;induction X;simpl;intros;auto.
rewrite S_Next_S_S in H;eauto.
Qed.

Lemma wfi_app_2:
  forall e X e0 T0, ((X == len e) -> false)-> 
  wfi (e ++ T0 :: e0) X -> wfi (e ++ e0) (S_Pred X (len e)).
Proof.
intros.
replace X with (S_Next (len e) (S_Pred X (len e))) in H0.
apply wfi_app_1 with T0;auto.
apply S_Next_Pred;auto.
Qed.


(* Relation (lel e1 e2) is the same as (length e1) <= (length e2).*)

Fixpoint lel (e1 e2:list A) {struct e1}:bool:=
  match e1, e2 with
  | nil        , _        => true
  | T :: e1' , nil        => false
  | T1 :: e1', T2 :: e2'  => lel e1' e2' 
  end.

Lemma lel_refl: forall e,  lel  e e.
Proof.
induction e;simpl;intros;b_auto.
Qed.

Hint Resolve lel_refl.

Lemma lel_trans: forall e1 e2 e3, lel  e1 e2 ->lel  e2 e3 ->lel  e1 e3.
Proof.
induction e1;induction e2;induction e3;simpl;intros;b_auto.
Qed.

Lemma lel_cons :forall e1 e2 M, lel e1 e2 -> lel e1 (M :: e2).
Proof. 
induction e1;intros;simpl;auto.
apply lel_trans with (a :: e1);eauto.
Qed.


Lemma lel_wfi: forall e e' X,  lel  e e' ->  wfi e X -> wfi e' X.
Proof.
induction e;induction e';induction X;simpl;intros;b_auto.
Qed.

Lemma app_lel: forall e e1 e2,  lel e1 e2 ->  lel (e ++ e1)  (e ++ e2).
Proof.
induction e;simpl;intros;b_auto.
Qed.

Lemma app_lel_cons: forall e1 e a,lel (e1 ++ e) (a :: e1 ++ e).
Proof.
induction e1;simpl in *;intros;auto.
apply lel_cons;auto.
Qed.


Lemma app_lel_2: forall e1 e2 e,  lel e1 e2 ->  lel (e1 ++ e)  (e2 ++ e).
Proof.
induction e1;induction e2;simpl in *;intros;b_auto.
apply lel_trans with (e2 ++ e);auto.
apply app_lel_cons;auto.
Qed.


(** Elements within lists. *)

Inductive inl :(list A) ->nat->A ->Prop:=
  | inl_0:forall e a, inl (a :: e) 0 a
  | inl_S:forall e X a b, inl e X a -> inl (b :: e) (S X) a.
 
Lemma inl_wf: forall e X a,  inl e X a -> wfi e X.
Proof.
induction e;induction X;simpl;intros;inversion H;eauto.
Qed.

Lemma inl_cons:forall e X T a, inl (a :: e) (S X) T -> inl e X T.
Proof.
intros;inversion H;auto.
Qed.

Lemma inl_inv:forall e X T1 T2,
    inl e X T1 -> inl  e X T2 -> T1 = T2.
Proof.
induction e;intros.
inversion H;auto.
induction X;intros.
inversion H;inversion H0;congruence.
apply IHe with X;auto.
apply inl_cons with a;auto.
apply inl_cons with a;auto.
Qed.

Lemma inl_ex: forall e X, wfi e X ->exists a, inl e X a.
Proof.
induction e;induction X;simpl;intros;b_auto.
exists a;apply inl_0.
elim (IHe X H).
intros x HX;exists x;apply inl_S;auto.
Qed.


Lemma inl_app_neq: forall e X e0 M N T, 
  (X == len e ->false) -> 
  inl (e ++ M :: e0)  X T ->  inl (e ++ N :: e0)  X T.
Proof.
induction e;induction X; simpl in *;intros;b_auto.
apply Contradiction;auto.
apply inl_S;auto.
inversion_clear H0;auto.
inversion H0;auto.
apply inl_0;auto.
inversion H0;auto.
apply inl_S;eauto.
Qed.


Lemma inl_app_cons: forall e e0 T, inl (e ++ T :: e0) (len e) T.
Proof.
induction e;simpl;intros;auto.
apply inl_0;auto.
apply inl_S;eauto.
Qed.

Lemma inl_app_1: forall e X e0 T0 T, 
   inl (e ++ T0 :: e0) (S_Next (len e) X) T ->inl (e ++ e0) X T.
Proof.
induction e;simpl;intros;auto.
rewrite S_Next_le in H;auto.
apply inl_cons with T0;auto.
induction X;simpl;intros;auto.
rewrite S_Next_gt in H;auto.
inversion H;auto;apply inl_0.
apply inl_S;auto.
apply IHe with T0;auto.
apply inl_cons with a;auto.
rewrite S_Next_S_S in H;auto.
Qed.


Lemma inl_app_2: forall e X e0 T0 T, 
 ((X == len e) -> false)-> 
  inl (e ++ T0 :: e0) X T ->inl (e ++ e0) (S_Pred X (len e)) T.
Proof.
intros.
replace X with (S_Next (len e) (S_Pred X (len e))) in H0.
apply inl_app_1 with T0;auto.
apply S_Next_Pred;auto.
Qed.

Fixpoint head (e:list A) (X:nat) {struct e}:list A:=
  match e, X with
  | nil     , _    => nil
  | T' :: e', 0    => nil
  | T' :: e', S X' => T' :: head e' X'
end.

Lemma head_len: forall e X , wfi e X ->len (head e X) = X.
Proof.
induction e;simpl;intros;b_auto.
induction X;simpl;intros;b_auto.
Qed.

Fixpoint tail (e:list A) (X:nat) {struct e}:list A:=
  match e, X with
  | nil     , _    => nil
  | T' :: e', 0    => e'
  | T' :: e', S X' => tail e' X'
end.


Lemma decomp_list: forall e X U, inl e X U ->
   e = head e X ++ U::tail e X.
Proof.
induction e;simpl;intros;b_auto.
inversion H;auto.
induction X;simpl;intros;b_auto.
inversion H;auto.
rewrite <-IHe with X U;auto.
inversion H;auto.
Qed.


(** Applying functions to lists *)

Section Maps.
Variable f:nat -> A -> A.

Fixpoint list_map (e:list A) {struct e}:list A:=
  match e with
  | nil      => nil
  | T' :: e' => f (len e') T' :: list_map e'
  end.

Lemma len_list_map:forall e,  len (list_map e) =len e.
Proof.
induction e;simpl;auto.
Qed.

Lemma lel_list_map:forall e, lel e (list_map e).
Proof.
induction e;simpl;auto.
Qed.

Lemma inl_map_app_le: forall e e0 X T,  
  len e <==  X -> inl (e ++ e0) X T -> inl (list_map e ++ e0 ) X T.
Proof.
induction e;simpl;intros;b_auto.
induction X;simpl;intros;b_auto.
apply inl_S;apply IHe;auto .
apply inl_cons with a;auto .
Qed.

Lemma inl_map_cons_le:forall e2 e1 X T1 T2 T0,
    inl (e2 ++ e1) X T1 -> inl (list_map e2 ++ T0 :: e1) (S X) T2 -> 
    len e2 <== X -> T1 = T2.
Proof.
induction e2;simpl;intros;b_auto.
apply inl_inv with e1 X;auto.
apply inl_cons with T0;auto.
induction X;simpl in *;intros;b_auto.
apply IHe2 with e1 X T0;auto.
apply inl_cons with a;auto.
apply inl_cons with (f (len e2) a);auto.
Qed.

Lemma inl_map_cons_gt:forall e2 e1 X  T1 T2 T0,
  inl (e2 ++ e1) X T1 -> inl (list_map e2 ++ T0 :: e1) X  T2 ->
  S X <== len e2 -> T2 = f (len e2 - S X) T1.
Proof.
induction e2;simpl;intros;b_auto.
induction X;simpl in *;intros;auto.
inversion H;inversion H0;rewrite H2.
rewrite <-H2;rewrite <-H6.
rewrite <-minus_n_O;auto.
simpl in *;rewrite IHe2 with e1 X T1 T2 T0;auto.
apply inl_cons with a;auto.
apply inl_cons with (f (len e2) a);auto.
Qed.

End Maps.



(** Mixed lists to be used as environmets in part2a. *)

Inductive list2:Set:=
  | nil2:list2
  | cons1:A -> list2 -> list2
  | cons2:A -> list2 -> list2.

Infix ":;" := cons1 (at level 60, right associativity).
Infix ";:" := cons2 (at level 60, right associativity).


Fixpoint lst (e:list2) {struct e}:list A:=
  match e with
  | nil2     => nil
  | T :; e'  => lst e'
  | T ;: e'  => T :: (lst e')
  end.

Notation "[ x ]" := (lst x)(at level 70).

 
Fixpoint len1 (e:list2){struct e}:nat:=
  match e with
  | nil2       => 0
  | T :; e'   => S (len1 e')
  | T ;: e'   => len1 e'
  end.
 
(** Concatenation of lists *)

Fixpoint list2_app (e:list2) (e0:list2){struct e}:list2:=
  match e with
  | nil2       => e0
  | T' :; e'   => T' :; (list2_app e' e0)
  | T' ;: e'   => T' ;: (list2_app e' e0)
  end.

Infix ".++" := list2_app (right associativity, at level 60).

Lemma app2_inv: forall (e1 e2 :list2) U V u v,
    e1 .++ U :; u = e2 .++ V :; v ->len1 e1 == len1 e2 -> U = V.
Proof.
induction e1;induction e2;simpl;intros;auto;try (inversion H);eauto.
apply Contradiction;auto.
apply Contradiction;auto.
Qed.


Lemma list2list_app : forall e e0,[e .++ e0] = [e] ++ [e0].
Proof.
induction e;simpl;intros;auto.
rewrite IHe with e0;auto.
Qed.


Lemma list2list_cons : forall e M, [M ;: e] = M :: ([e]).
Proof.
induction e;simpl;intros;auto.
Qed.

(** Elements within lists. *)

Inductive ine :list2 ->nat->A ->Prop:=
  | ine_0:forall e a, ine (a :; e) 0 a
  | ine_S1:forall e X a b, ine e X a -> ine (b :; e) (S X) a
  | ine_S2:forall e X a b, ine e X a -> ine (b ;: e) X a.

Lemma ine_cons1:forall e X T a, ine (a :; e) (S X) T -> ine e X T.
Proof.
intros;inversion H;auto.
Qed.

Lemma ine_cons2:forall e X T a, ine (a ;: e) X T -> ine e X T.
Proof.
intros;inversion H;auto.
Qed.


Lemma ine_app_cons: forall e e0 T, ine (e .++ T :; e0) (len1 e) T.
Proof.
induction e;simpl;intros;auto.
apply ine_0.
apply ine_S1;auto.
apply ine_S2;auto.
Qed.

Lemma ine_app_cons_2: forall e e0 N X T, 
  ine (e .++ N ;: e0) X T ->ine (e .++ e0) X T.
Proof.
induction e;simpl;intros;auto.
inversion H;auto.
induction X;simpl;intros;auto.
inversion H;auto.
apply ine_0.
apply ine_S1.
apply IHe with N;auto.
inversion H;auto.
apply ine_S2.
apply IHe with N;auto.
inversion H;auto.
Qed.


Lemma ine_cons: forall e e0 N X T, 
  ine (e .++ e0) X T -> ine (e .++ N ;: e0) X T.
Proof.
induction e;simpl;intros;eauto.
apply ine_S2;auto.
induction X;simpl;intros;auto.
inversion H;auto.
apply ine_0.
apply ine_S1;auto.
inversion H;auto.
apply ine_S2;auto.
inversion H;auto.
Qed.


Lemma ine_app:  forall e X e0 T0 T, 
  ine (e .++ e0) X T -> ine (e .++ T0 :; e0) (S_Next (len1 e) X) T.
Proof.
induction e;simpl;intros;auto.
rewrite S_Next_le;auto.
apply ine_S1;auto.
induction X;simpl;intros;auto.
rewrite S_Next_gt;auto.
inversion H;auto;apply ine_0.
rewrite S_Next_S_S;auto.
apply ine_S1;auto.
apply IHe;auto.
apply ine_cons1 with a;auto.
apply ine_S2;auto.
apply IHe;auto.
inversion H;auto.
Qed.


Lemma ine_app1: forall e X e0 T0 T, 
  ine (e .++ T0 :; e0) (S_Next (len1 e) X) T ->ine (e .++ e0) X T.
Proof.
induction e;simpl;intros;auto.
rewrite S_Next_le in H;auto.
apply ine_cons1 with T0;auto.
induction X;simpl;intros;auto.
rewrite S_Next_gt in H;auto.
inversion H;auto;apply ine_0.
rewrite S_Next_S_S in H;auto.
apply ine_S1;auto.
apply IHe with T0;auto.
apply ine_cons1 with a;auto.
apply ine_S2;auto.
apply IHe with T0;auto.
inversion H;auto.
Qed.

Lemma ine_app_2: forall e X e0 T0 T, 
  ((X == len1 e) -> false)-> 
  ine (e .++ T0 :; e0) X T -> ine (e .++ e0) (S_Pred X (len1 e)) T.
Proof.
intros.
intros;apply ine_app1 with T0;auto.
rewrite S_Next_Pred;auto.
Qed.


Fixpoint head1 (e:list2) (X:nat) {struct e}:list2:=
  match e, X with
  | nil2    , _    => nil2
  | T' :; e', 0    => nil2
  | T' :; e', S X' => T' :; head1 e' X'
  | T' ;: e', _    => T' ;: head1 e' X
end.

Fixpoint tail1 (e:list2) (X:nat) {struct e}:list2:=
  match e, X with
  | nil2    , _    => nil2
  | T' :; e', 0    => e'
  | T' :; e', S X' => tail1 e' X'
  | T' ;: e', _    => tail1 e' X
end.


Lemma decomp_list2: forall e X U, 
   ine e X U -> e = head1 e X.++ U:;tail1 e X.
Proof.
induction e;simpl;intros;b_auto.
inversion H;auto.
induction X;simpl;intros;b_auto.
inversion H;auto.
rewrite <-IHe with X U;auto.
apply ine_cons1 with a;auto.
rewrite <-IHe with X U;auto.
apply ine_cons2 with a;auto.
Qed.

Lemma head_len1: forall e X U, ine e X U ->len1 (head1 e X) = X.
Proof.
induction e;simpl;intros;auto.
inversion H;auto.
induction X;simpl;intros;b_auto.
rewrite IHe with X U;auto.
apply ine_cons1 with a;auto.
rewrite IHe with X U;auto.
apply ine_cons2 with a;auto.
Qed.

Lemma head1_prop_0:  forall e e0 T, 
    len ([head1 (e .++  T :; e0) (len1 e)]) = len ([e]).
Proof.
induction e;simpl;intros;auto.
Qed.

Lemma head1_prop_1: forall e e0 X,
     len1 e <== X -> len ([e]) <== len ([head1(e .++ e0) X]) . 
Proof.
induction e;simpl;intros;auto.
induction X;intros;simpl;b_auto.
Qed.

Lemma head1_prop_2: forall e e0 X,
    S X <== len1 e -> len ([head1(e .++ e0) X]) <== len ([e]). 
Proof.
induction e;simpl;intros;auto.
induction X;intros;simpl;b_auto.
induction X;intros;simpl;b_auto.
Qed.

Lemma head1_cons1:
  forall e X e0 T, 
  len ([head1 (e .++ T :; e0) (S_Next (len1 e) X)]) = len ([head1 (e .++ e0) X]).
Proof.
induction e;simpl;intros;auto.
induction X;simpl;intros;auto.
rewrite S_Next_S_S;simpl;auto.
Qed.


Lemma head1_cons1_neq:
  forall e X e0 T, 
  ((X == len1 e) -> false)-> 
  len ([head1 (e .++ T :; e0) X]) = len ([head1 (e .++ e0) (S_Pred X (len1 e))]).
Proof.
intros.
apply trans_eq with (len ([head1 (e .++ T :; e0) (S_Next (len1 e) (S_Pred X (len1 e)))])).
rewrite S_Next_Pred;auto.
rewrite head1_cons1 with e (S_Pred X (len1 e)) e0 T;auto.
Qed.


Lemma head1_cons2_le:  forall e e0 T X,  
 len1 e <== X -> len ([head1 (e .++ T ;: e0) X]) = S (len ([head1 (e .++ e0) X])).
Proof.
induction e;simpl;intros;eauto.
induction X;simpl;intros;eauto.
Qed.

Lemma head1_cons2_gt: forall e e0 T X,  
  (S X <==  len1 e) -> 
  len ([head1 (e .++ T ;: e0) X]) = len ([head1 (e .++ e0) X]).
Proof.
induction e;simpl;intros;eauto.
induction X;simpl;intros;eauto.
Qed.


Lemma head1_cons2:  forall e e0 M N X,
   len ([head1 (e .++ M ;: e0) X]) = len ([head1 (e .++ N ;: e0) X]).
Proof.
induction e;simpl;intros;eauto.
induction X;simpl;intros;eauto.
Qed.


(** Applying functions to lists *)

Section Maps2.
Variable f:nat -> A -> A.

Fixpoint list2_map (e:list2) {struct e}:list2:=
  match e with
  | nil2        => nil2 
  | T' :; e'    => f (len ([e'])) T' :; list2_map e'
  | T' ;: e'    => f (len ([e'])) T' ;: list2_map e'
  end.


Lemma list2_apps: forall e e0,
  [list2_map e .++ e0] =  list_map f ([e]) ++ [e0].
Proof.
induction e;simpl;intros;b_auto;simpl.
rewrite IHe;auto.
Qed.

Lemma head1_map: forall e e0 X,
  len ([head1 (list2_map e .++ e0) X]) =  len ([head1 (e .++ e0) X]).
Proof.
induction e;simpl;intros;b_auto;simpl.
induction X;simpl;intros;auto.
Qed.

Lemma ine_app_le:  forall e e0 X T,  
  len1 e <==  X ->ine (e .++ e0) X T -> ine (list2_map e .++ e0) X T.
Proof.
induction e;simpl;intros;auto.
induction X;simpl;intros;auto.
b_auto.
apply ine_S1;apply IHe;auto .
apply ine_cons1 with a;auto .
apply ine_S2;apply IHe;auto .
apply ine_cons2 with a;auto .
Qed.


Lemma ine_app_gt: forall e e0 X T,
  (S X <== len1 e)-> ine (e .++ e0) X T ->
  ine (list2_map e .++ e0) X (f (len ([e]) - len ([head1 (e .++ e0) X]))  T).
Proof.
induction e;simpl;intros;b_auto.
induction X;simpl in *;intros;auto.
rewrite <-minus_n_O;auto.
inversion H0;apply ine_0.
simpl in *.
apply ine_S1;auto.
apply IHe;auto.
apply ine_cons1 with a;auto.
apply ine_cons1 with (f (len ([e])) a);auto.
apply ine_S1;auto.
apply ine_S2;auto.
apply IHe;auto.
apply ine_cons2 with a;auto.
Qed.


End Maps2.

End Lists.


Hint Resolve lel_refl.

  
(* ============================================================================ *)
(** * Shifting and Substitution of Types *)
(* ============================================================================ *)
 
Inductive type:Set:=
  | top  :type
  | ref  :nat ->type
  | arrow:type -> type -> type
  | all  :type -> type -> type.

Infix "-->"     := arrow (at level 60, right associativity).
Infix ".`"      := all (at level 60, right associativity).

(**  
By using coercion [ref:nat >-> type] we identify [X] with [ref X].
*)

Coercion  ref:nat >-> type.

Fixpoint tshift (X:nat) (T:type) {struct T}:type:=
  match T with
  | top       => top
  | ref Y     => S_Next X Y
  | T1 --> T2 => (tshift X T1) --> (tshift X T2)
  | T1 .` T2  => (tshift X T1) .` (tshift (S X) T2)
  end.           
     
Lemma tshift_tshift: forall T n n',
  n <== n' -> tshift (S n') (tshift n T) = tshift n (tshift n' T).
Proof.
induction T;intros;auto.
unfold tshift;unfold S_Next.
apply Decide with (n' <== n);intro;b_rewrite.
apply Decide with (n0 <== n);intro;b_rewrite.
apply Decide with (n0 <== S n);intro;b_rewrite.
apply Decide with (S n' <== S n);intro;b_rewrite.
apply Contradiction;apply H2.
apply n_le_trans with n;auto;apply le_n_Sn;auto.
apply Contradiction;apply H1;apply n_le_trans with n';auto.
apply Decide with (n0 <== n);intro;b_rewrite.
apply Decide with (S n' <== S n);intro;b_rewrite.
apply Decide with (S n' <== n);intro;b_rewrite.
apply Contradiction;apply H1;apply n_le_trans with n';auto.
apply n_le_trans with (S n');auto;apply le_n_Sn.
simpl; apply f_equal2 with (f:= arrow); auto.
simpl; apply f_equal2 with (f:= all); auto.
Qed.

Notation  "+" := (tshift 0) (at level 70).

Lemma tshift_tshift_prop: forall T n,
  tshift (S n) (+ T) = + (tshift n T).
Proof.
intros T n.
apply tshift_tshift;auto.
Qed.

(** Operator 'lift' is operator 'tshift 0', applied X times.*) 

Fixpoint lift (X:nat)(T:type){struct X}:type:=
  match X with
  | 0     => T
  | S X' => + (lift X' T)
  end.

Lemma lift_tshift:forall X T,
    lift (S X) T = lift X (+ T).
Proof.
induction X;intros;auto.
simpl;rewrite <-IHX;auto.
Qed.

Lemma lift_tshift_0:forall X T,
    lift X (+ T) = + (lift X T).
Proof.
intros X T;rewrite <-lift_tshift;auto.
Qed.

Lemma tshift_lift_le:forall Y X T,
   Y <== X -> tshift Y (lift X T) = lift (S X) T.
Proof.
induction Y;intros;b_auto.
induction X;intros;auto.
apply Contradiction;apply not_le_S_n with Y;auto.
simpl;rewrite tshift_tshift_prop;auto.
apply f_equal2 with (f:=tshift);auto.
simpl in *;rewrite <-IHY with X T;auto.
Qed.

Lemma tshift_lift:forall Y X T,
   X <== Y -> tshift Y (lift X T) = lift X (tshift (Y - X) T).
Proof.
induction X;intros;simpl;auto.
rewrite <-minus_n_O;auto.
rewrite <-lift_tshift_0.
rewrite IHX;auto.
replace (Y - X) with (S (Y - (S X))).
rewrite tshift_tshift_prop;auto.
rewrite lift_tshift_0;auto.
rewrite minus_Sn_m;simpl;auto.
apply nat_le_leq;auto.
apply n_le_trans with (S X);auto.

Qed.


Fixpoint tsubst (T':type)(X:nat)(T:type){struct T}:type:=
  match T with
  | top       => top
  | ref Y      => if (Y == X) then T' else  (S_Pred Y X)
  | T1 --> T2  => (tsubst T' X T1) --> (tsubst T' X T2)
  | T1 .` T2   => (tsubst T' X T1) .` (tsubst (+ T') (S X) T2) 
  end.  

Lemma tsubst_tshift: forall T n T',
   tsubst T' n (tshift n T) = T.
Proof.
unfold tshift;fold tshift;unfold tsubst;fold tsubst.
induction T;simpl;intros;auto.
apply Decide with (S_Next n0 n == n0).
simpl;unfold S_Next.
apply Decide with (n0 <== n);intro;b_rewrite.
intros;apply Contradiction;apply not_le_S_n with n;auto.
apply n_le_trans with n0;auto.
intros;apply Contradiction;apply H;auto.
intro;b_rewrite.
rewrite S_Pred_Next;auto.
simpl; apply f_equal2 with (f:= arrow); auto.
simpl; apply f_equal2 with (f:= all); auto.
Qed.
  
Lemma tshift_tsubst_1: forall T T' n n',
  n <== n' ->
  tsubst (tshift n T') (S n')(tshift n T) =
  tshift n (tsubst T' n' T).
Proof.
induction T;simpl;intros;auto.
unfold S_Next.
apply Decide with (n0 <== n);intro;b_rewrite.
apply Decide with (n == n');intro;b_rewrite.
apply Decide with (S n == S n');intro;b_rewrite.
apply Contradiction;apply H2;apply eq_S;auto.
apply Decide with (S n == S n');intro;b_rewrite.
apply Contradiction;apply H1;apply b_eq_add_S;auto.
rewrite S_Pred_S_S;simpl;unfold S_Next.
apply Decide with (n0 <== S_Pred n n');intro;b_rewrite.
apply Contradiction;apply H3;simpl;unfold S_Pred.
apply Decide with (n <== n');intro;b_rewrite.
apply n_le_trans with n';auto.
apply b_le_or_ge;auto;intro;apply H4.
apply n_le_trans with (S (pred n));auto.
rewrite b_S_pred;auto.
intros;apply Contradiction;apply H4.
apply n_le_trans with 0;auto.
apply Decide with (n == S n');intro;b_rewrite.
apply Contradiction;apply H0;apply n_le_trans with (S n');auto.
apply n_le_trans with n';auto;apply le_n_Sn.
apply Decide with (n == n');intro;b_rewrite.
apply Contradiction;apply H0;apply n_le_trans with n';auto.
simpl;unfold S_Pred.
apply Decide with (n <== n');intro;b_rewrite.
apply Decide with (n <== S n');intro;b_rewrite.
simpl;unfold S_Next;b_rewrite.
apply Contradiction;apply H4;apply n_le_trans with n';auto.
apply Decide with (n <== S n');intro;b_rewrite.
apply Contradiction;apply H3.
apply n_le_trans with (pred (S n'));auto.
apply b_le_or_ge;auto;intro.
apply H1.
rewrite b_le_ge_eq with n (S n');auto;apply le_pred_2;auto.
simpl;unfold S_Next.
apply Decide with (n0 <== pred n);intro;b_rewrite.
apply Contradiction;apply H0.
apply n_le_trans with (pred n);auto;apply le_pred_n.
simpl; apply f_equal2 with (f:= arrow); auto.
simpl; apply f_equal2 with (f:= all); auto.
rewrite <-tshift_tshift_prop;auto.
Qed.

Definition f_tsubst (T0:type)(X :nat)(T:type):=tsubst (lift X T0) X T.

Notation "  X [=>] T0" := (f_tsubst T0 X)(at level 70).

Lemma tshift_tsubst_prop_1:forall X T T0,
  (S X [=>] T0) (+ T) =  + ((X [=>] T0) T).
Proof.
unfold f_tsubst;intros;simpl;apply tshift_tsubst_1;auto.
Qed.

Lemma tsubst_lift_le:  forall Y X T N, 
  Y <== X -> (Y [=>]N) (lift (S X) T) = lift X T.
Proof.
induction Y;simpl;intros;b_auto.
unfold f_tsubst ;rewrite tsubst_tshift;auto.
rewrite tshift_tsubst_prop_1;auto.
induction X;simpl;intros;b_auto.
simpl in *;apply f_equal2 with (f:=tshift);eauto.
Qed.


Lemma tsubst_lift_gt: forall  X Y T N, 
  X <== Y ->lift X ((Y - X [=>] N) T) = (Y [=>] N) (lift X T).
Proof.
induction X;simpl;intros;b_auto.
rewrite <-minus_n_O;auto.
rewrite  <-lift_tshift_0.
rewrite <-tshift_tsubst_prop_1;auto.
replace (S (Y - S X)) with (Y - X).
rewrite IHX;auto.
rewrite  <-lift_tshift_0;auto.
apply n_le_trans with (S X);auto.
rewrite minus_Sn_m;simpl;auto.
apply nat_le_leq;auto.
Qed.


Lemma tshift_tsubst_2: forall T T' n n', 
  n <== n' ->
  tshift n' (tsubst T' n T) =  tsubst (tshift n' T') n (tshift (S n') T).
Proof.
induction T;simpl;intros;auto.
apply Decide with (S_Next (S n') n == n0).
apply Decide with (n == n0);intro;b_rewrite.
unfold S_Next;intro;b_rewrite.
unfold S_Next.
apply Decide with (S n' <== n);intro;b_rewrite.
intro;apply Contradiction;apply not_le_S_n with n.
apply n_le_trans with n0;auto.
apply n_le_trans with (S n');auto.
apply n_le_trans with n';auto;apply le_n_Sn.
intro;apply Contradiction;apply H0;auto.
unfold S_Next;intro;b_rewrite.
apply Decide with (n == n0);intro;b_rewrite.
apply Contradiction;apply H0;auto.
apply Decide with (S n' <== n);intro;b_rewrite.
apply Contradiction;apply not_le_S_n with n'.
apply n_le_trans with n;auto;apply n_le_trans with n0;auto.
apply Decide with (S n' <== n);intro;b_rewrite.
simpl;unfold S_Next;unfold S_Pred.
apply Decide with (n <== n0);intro;b_rewrite.
apply Contradiction;apply not_le_S_n with n'.
apply n_le_trans with n;auto;apply n_le_trans with n0;auto.
apply Decide with (S n <== n0);intro;b_rewrite.
apply Contradiction;apply H3.
apply n_le_trans with (S n);auto;apply le_n_Sn.
apply Decide with (n' <== pred n);intro;b_rewrite.
rewrite b_pred_Sn;rewrite b_S_pred;auto.
intros;apply Contradiction;apply not_le_S_n with n'.
apply n_le_trans with n;auto;apply n_le_trans with 0;auto.
apply Contradiction;apply H5;auto.
apply b_le_add_S;apply n_le_trans with n;auto.
rewrite b_S_pred;auto.
intros;apply Contradiction;apply not_le_S_n with n'.
apply n_le_trans with 0;auto.
apply n_le_trans with n;auto.
simpl;apply Decide with (n' <== S_Pred n n0).
unfold S_Pred.
apply Decide with (n <== n0);intro;b_rewrite.
intros;apply Contradiction;apply H1.
rewrite b_le_ge_eq with n n0;auto.
apply n_le_trans with n';auto.
intros;apply Contradiction;apply H2;auto.
apply n_le_trans with (S (pred n));auto.
rewrite b_S_pred;auto.
intros;apply Contradiction;apply H1;auto.
apply n_eq_trans with 0.
rewrite <- le_eq_O with n;auto.
rewrite <- le_eq_O with n0;auto.
apply n_le_trans with n';auto;apply n_le_trans with (pred n);auto.
apply n_le_trans with (pred 0);auto;apply le_pred;auto.
unfold S_Next;intro;b_rewrite.
simpl; apply f_equal2 with (f:= arrow); auto.
simpl; apply f_equal2 with (f:= all); auto.
rewrite <-tshift_tshift_prop;eauto.
Qed.


Lemma tshift_tsubst_prop_2: forall X T T0,
  tshift X ((0 [=>] T0) T) =  (0 [=>] tshift X T0) (tshift (S X) T).
Proof.
unfold f_tsubst;intros;simpl;apply tshift_tsubst_2;auto.
Qed.


Lemma tsubst_tsubst: forall T U V n n',
  n <== n' ->
  tsubst V n' (tsubst U n T) =
  tsubst (tsubst V n' U) n (tsubst (tshift n V) (S n') T) .
Proof.
induction T;simpl;intros;auto.
apply Decide with (n == n0);intro;b_rewrite.
apply Decide with (n == S n');intro;b_rewrite.
apply Contradiction;apply not_le_S_n with n'.
apply n_le_trans with n;auto.
apply n_le_trans with n0;auto.
simpl;apply Decide with (S_Pred n (S n') == n0);intro;b_rewrite.
apply Contradiction;apply H2;auto.
unfold S_Pred;simpl.
apply Decide with (n <== S n');intro;b_rewrite.
apply Contradiction;apply H3;auto.
apply n_le_trans with n0;auto;apply n_le_trans with n';auto.
apply Decide with (n == S n');intro;b_rewrite.
unfold S_Pred;simpl.
apply Decide with (n <== n0);intro;b_rewrite.
apply Contradiction;apply not_le_S_n with n';auto.
apply n_le_trans with n;auto;apply n_le_trans with n0;auto.
apply Decide with (pred n == n');intro;b_rewrite.
rewrite tsubst_tshift;auto.
apply Contradiction;apply H3;auto.
apply b_eq_add_S;auto;apply n_eq_trans with n;auto.
rewrite b_S_pred;auto;intros;apply H2.
apply n_le_trans with 0;auto.
simpl;apply Decide with (S_Pred n n0 == n');unfold S_Pred.
apply Decide with (n <== n0);intro;b_rewrite.
intros;apply Contradiction;apply H0;auto.
rewrite b_le_ge_eq with n n0;auto;apply n_le_trans with n';auto.
intros;b_rewrite.
apply Decide with (n <== S n');intro;b_rewrite.
apply Contradiction;apply H1;auto.
apply n_eq_trans with (S (pred n));auto.
rewrite b_S_pred;auto.
intro;apply Contradiction;apply H2;auto.
apply n_le_trans with 0;auto.
apply Contradiction;apply H4;auto.
apply n_le_trans with (S (pred n));auto.
rewrite b_S_pred;auto.
intro;apply Contradiction;apply H2;auto.
apply n_le_trans with 0;auto.
apply Decide with (n <== n0);intro;b_rewrite.
intros;b_rewrite.
apply Decide with (n <== n');intro;b_rewrite.
apply Decide with (n <== S n');intro;b_rewrite.
b_rewrite;b_rewrite.
apply Contradiction;apply H5;auto.
apply n_le_trans with n';auto.
apply Contradiction;apply H4;auto.
apply n_le_trans with n0;auto.
apply Decide with (n <== S n');intro;b_rewrite.
apply Decide with (pred n <== n');intro;b_rewrite.
intros;b_rewrite.
apply Contradiction;apply H4;auto.
apply b_le_add_S;auto.
apply n_le_trans with n;auto.
rewrite b_S_pred;auto.
intro;apply Contradiction;apply H2;auto.
apply n_le_trans with 0;auto.
apply Decide with (pred n <== n');intro;b_rewrite.
apply Contradiction;apply H3;auto.
apply n_le_trans with (S (pred n));auto.
rewrite b_S_pred;auto.
intro;apply Contradiction;apply H3;auto.
apply n_le_trans with 0;auto.
intros;b_rewrite.
apply Decide with (pred n == n0);intro;b_rewrite.
apply Contradiction;apply H4;auto.
apply n_le_trans with n0;auto.
apply Decide with (pred n <== n0);intro;b_rewrite.
apply Contradiction;apply H2;auto.
apply b_le_or_ge.
intros;apply H6.
rewrite b_le_ge_eq with (pred n) n0;auto.
apply b_le_add_S.
apply n_le_trans with n;auto.
rewrite b_S_pred;auto.
intro;apply Contradiction;apply H2;auto.
apply n_le_trans with 0;auto.
simpl; apply f_equal2 with (f:= arrow); auto.
simpl; apply f_equal2 with (f:= all); auto.
rewrite <-tshift_tsubst_1;auto.
rewrite <-tshift_tshift_prop;auto.
Qed.


Lemma tsubst_tsubst_prop:forall X T U V,
  (X [=>] V)((0 [=>] U) T) = (0 [=>] (X [=>] V) U) ((S X [=>] V) T).
Proof.
intros;unfold f_tsubst;simpl;apply tsubst_tsubst;auto.
Qed.
