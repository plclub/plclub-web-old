(*********************************************************)
(*   Submission for PoplMark challenges                  *)
(*   Jevgenijs Sallinens, August 2005                    *) 
(*   Definitions for subtyping relation (sub_defs.v)     *) 
(*********************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Bool.
Require Import tactics.

(******************************************************************************************)
(*          Interface for module of (pseudo) natural numbers                              *)
(******************************************************************************************)

Module Type T_Nat.

Parameter t_nat:Set.
Parameter t_O:t_nat.
Parameter t_S:t_nat ->t_nat.
Parameter t_pred:t_nat ->t_nat.
Parameter beq_t_nat:t_nat ->t_nat->bool.
Axiom t_nat_eq_dec:forall (n m:t_nat), {n = m} + {n <> m}.
Axiom t_S_pred:forall (n:t_nat), n <> t_O ->t_S (t_pred n) = n.
Axiom t_O_S:forall (n:t_nat),  t_S n <> t_O.
Axiom t_pred_Sn:forall (n:t_nat),  (t_pred (t_S n)) = n.
Axiom beq_t_nat_refl:forall n, true = beq_t_nat n n.
Axiom beq_t_nat_eq:forall x y, true = beq_t_nat x y -> x = y.

Parameter t_semi_P:t_nat ->t_nat->t_nat.
Parameter t_semi_S:t_nat ->t_nat->t_nat.

Axiom t_semi_S_P:
  forall  (x x':t_nat),
  x <> x' ->t_semi_S x' (t_semi_P x x') =  x.

Axiom t_semi_S_0_n:
  forall  (n:t_nat), t_semi_S t_O n = t_S n.

Axiom t_semi_S_S_0:
  forall  (n:t_nat),t_semi_S (t_S n) t_O  = t_O. 

Axiom t_semi_S_1:
  forall  (n n':t_nat), n <> t_O ->
  t_pred (t_semi_S (t_S n') n) = t_semi_S n' (t_pred n).

Axiom t_semi_S_2:
  forall  (n n':t_nat), n <> t_O ->
  t_semi_S (t_S n') n = t_S (t_semi_S n' (t_pred n)).

Axiom t_semi_S_3:
  forall  (n n':t_nat), 
  n <> t_O -> t_semi_S (t_S n') n <> t_O.


Inductive typ:Set:=
  | t_var:t_nat ->typ
  | top :typ
  | arrow:typ -> typ -> typ
  | all :typ -> typ -> typ.

Fixpoint tshift (X:t_nat) (T:typ) {struct T}:typ:=
  match T with
  | t_var Y     => t_var (t_semi_S X Y)
  | top         => top
  | arrow T1 T2 => arrow (tshift X T1) (tshift X T2)
  | all T1 T2   => all (tshift X T1) (tshift (t_S X) T2)
  end.           

Fixpoint tsubst (T:typ) (X:t_nat) (T':typ) {struct T}:typ:=
  match T with
  | t_var Y     => if (t_nat_eq_dec Y X) then T' else t_var (t_semi_P Y X)
  | top         => top
  | arrow T1 T2 => arrow (tsubst T1 X T') (tsubst T2 X T')
  | all T1 T2   => all (tsubst T1 X T') (tsubst T2 (t_S X) (tshift t_O T'))
  end.

Axiom tshift_tshift_prop:
  forall (T:typ)(n:t_nat),
  tshift t_O (tshift n T) = tshift (t_S n) (tshift t_O T).

Axiom tshift_tsubst_prop_1:
  forall (n:t_nat) (T T':typ),
  tshift t_O (tsubst T n T') =
  tsubst  (tshift t_O T) (t_S n) (tshift t_O T').

Axiom tshift_tsubst_prop_2:
  forall (n:t_nat) (T T':typ),
  (tshift n (tsubst T t_O T')) =
  (tsubst (tshift (t_S n) T) t_O (tshift n T')).

Axiom tsubst_tshift_prop:
  forall (T T':typ), T = tsubst (tshift t_O T) t_O T'.


Axiom tsubst_tsubst_prop:
  forall (n:t_nat) (T U V:typ),
  (tsubst (tsubst T t_O U) n V) =
  (tsubst (tsubst T (t_S n) (tshift t_O V)) t_O (tsubst U n V)).

End T_Nat.
(******************************************************************************************)

Require Import Arith.
Require Import Omega.

(******************************************************************************************)
(*                 Module of (pseudo) natural numbers                                     *)
(******************************************************************************************)


Module M_T_Nat:T_Nat.
Definition t_nat:=nat.
Definition t_O:=O.
Definition t_S:=S.
Definition t_pred:=pred.

Lemma t_S_pred:forall (n:nat), n <> O ->S (pred n) = n.
Proof.
intros;omega.
Qed.

Lemma t_O_S:forall (n:nat),  S n <> O.
Proof.
intros;auto with arith.
Qed.

Lemma t_pred_Sn:forall (n:nat), pred (S n) = n.
Proof.
intros;auto with arith.
Qed.

Lemma t_nat_eq_dec:forall (n m:nat), {n = m} + {n <> m}.
Proof.
induction n; induction m; auto.
elim (IHn m); auto.
Defined.

Fixpoint beq_t_nat (n m:nat) {struct n}:bool:=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n1, S m1 => beq_t_nat n1 m1
  end.

Lemma beq_t_nat_refl:forall n, true = beq_t_nat n n.
Proof.
  intro x; induction x; simpl in |- *; auto.
Qed.

Lemma beq_t_nat_eq:forall x y, true = beq_t_nat x y -> x = y.
Proof.
  double induction x y; simpl in |- *.
    reflexivity.
    intros; discriminate H0.
    intros; discriminate H0.
    intros; case (H0 _ H1); reflexivity.
Qed.

Definition t_semi_P (Y X:nat):= if (le_gt_dec Y X) then Y else (pred Y).
Definition t_semi_S (Y X:nat):= if (le_gt_dec Y X) then S X else X.

Ltac nat_cases:=
  match goal with
  | |- ?H =>
      match H with
      | context [t_nat_eq_dec ?n ?n'] =>
          case (t_nat_eq_dec n n');auto
      | context [le_gt_dec ?n ?n'] =>
          case (le_gt_dec n n');auto
      | context C [(lt_eq_lt_dec ?n ?n')] =>
          case (lt_eq_lt_dec n n'); [intro s; case s; clear s;auto |auto ]
      end
end.


Lemma t_semi_S_P:
  forall  (x x':nat),
  x <> x' ->(t_semi_S x' (t_semi_P x x')) =  x.
Proof.
intros n n';unfold t_semi_P;unfold t_semi_S.
repeat nat_cases;intros;omega.
Qed.


Lemma t_semi_S_0_n:
  forall  (n:nat), t_semi_S 0 n = S n.
Proof.
auto.
Qed.

Lemma t_semi_S_S_0:
  forall  (n:nat),t_semi_S (S n) 0  = 0. 
Proof.
auto.
Qed.

Lemma t_semi_S_1:
  forall  (n n':nat), n <> 0 ->
  pred (t_semi_S (S n') n) = t_semi_S n' (pred n).
Proof.
intros n n';unfold t_semi_S.
repeat nat_cases;intros;omega.
Qed.           

Lemma t_semi_S_2:
  forall  (n n':nat), n <> 0 ->
  t_semi_S (S n') n = S (t_semi_S n' (pred n)).
Proof.
intros n n';unfold t_semi_S.
repeat nat_cases;intros;omega.
Qed.

Lemma t_semi_S_3:
  forall  (n n':nat), 
  n <> 0 ->t_semi_S (S n') n <> 0.
Proof.
intros n n';unfold t_semi_S.
repeat nat_cases;intros;auto with arith.
Qed. 


Inductive typ:Set:=
  | t_var:nat ->typ
  | top:typ
  | arrow:typ -> typ -> typ
  | all:typ -> typ -> typ.

Fixpoint tshift (X:nat) (T:typ) {struct T}:typ:=
  match T with
  | t_var Y      => t_var (t_semi_S X Y)
  | top         => top
  | arrow T1 T2 => arrow (tshift X T1) (tshift X T2)
  | all T1 T2   => all (tshift X T1) (tshift (S X) T2)
  end.           

Fixpoint tsubst (T:typ) (X:nat) (T':typ) {struct T}:typ:=
  match T with
  | t_var Y      => if (t_nat_eq_dec Y X) then T' else t_var (t_semi_P Y X)
  | top         => top
  | arrow T1 T2 => arrow (tsubst T1 X T') (tsubst T2 X T')
  | all T1 T2   => all (tsubst T1 X T') (tsubst T2 (S X) (tshift 0 T'))
  end.

  
Ltac t_var_case:=
  unfold tshift; unfold tsubst; unfold t_semi_S;unfold t_semi_P;fold tshift; fold tsubst;nat_cases.

Ltac common_cases2 n T:=
  simpl; generalize n; clear n; induction T; intros n''; intros;
    [ repeat t_var_case;
      try (intros; assert False; [ omega | contradiction ])
    | trivial
    | simpl; apply f_equal2 with (f:= arrow); trivial
    | simpl; apply f_equal2 with (f:= all); trivial ].
    
 
Lemma tshift_tshift:
  forall  (T:typ)(n n':nat),
  tshift n (tshift (n + n') T) = tshift (S (n + n')) (tshift n T).
Proof.
intros T n n'; unfold tshift;fold tshift;common_cases2 n T;auto.
apply IHT2 with (n:=(S n''));auto.
Qed.

Lemma tshift_tshift_prop:
  forall (T:typ)(n:nat),
  tshift 0 (tshift n T) = tshift (S n) (tshift 0 T).
Proof.
intros T n.
replace n with (0 + n).
apply tshift_tshift;auto.
omega.
Qed.


Lemma tshift_tsubst_1:
  forall (n n':nat) (T T':typ),
  tshift n (tsubst T (n + n') T') =
  tsubst (tshift n T) (S (n + n')) (tshift n T').
Proof.
intros n n' T; common_cases2 n T.
intros; apply f_equal with (f:= t_var); omega.
rewrite tshift_tshift_prop; apply (IHT2 (S n'')).
Qed.

Lemma tshift_tsubst_prop_1:
  forall (n:nat) (T T':typ),
  tshift 0 (tsubst T n T') =
  tsubst  (tshift 0 T) (S n) (tshift 0 T').
Proof.
intros n T T'.
replace n with (0 + n).
apply tshift_tsubst_1;auto.
omega.
Qed.

Lemma tshift_tsubst_2:
  forall (n n':nat) (T T':typ),
  (tshift (n + n') (tsubst T n T')) =
  (tsubst (tshift (S (n + n')) T) n (tshift (n + n') T')).
Proof.
intros n n' T; common_cases2 n T.
intros; apply f_equal with (f:= t_var); omega.
rewrite tshift_tshift_prop; apply (IHT2 (S n'')).
Qed.

Lemma tshift_tsubst_prop_2:
  forall (n:nat) (T T':typ),
  (tshift n (tsubst T 0 T')) =
  (tsubst (tshift (S n) T) 0 (tshift n T')).
Proof.
intros n T T'.
replace n with (0 + n).
apply tshift_tsubst_2;auto.
omega.
Qed.

Lemma tsubst_tshift:
  forall (T:typ) (n:nat),forall (T':typ), T = tsubst (tshift n T) n T'.
Proof.
unfold tshift;fold tshift;unfold tsubst;fold tsubst.
intros T n; common_cases2 n T.
Qed.

Lemma tsubst_tshift_prop:
  forall (T T':typ), T = tsubst (tshift 0 T) 0 T'.
Proof.
intros T n.
apply tsubst_tshift;auto.
Qed.

Lemma tsubst_tsubst:
  forall (n n':nat) (T U V:typ),
  (tsubst (tsubst T n U) (n + n') V) =
  (tsubst (tsubst T (S (n + n')) (tshift n V)) n (tsubst U (n + n') V)).
Proof.
intros n n' T; common_cases2 n T.
intros; apply tsubst_tshift.
rewrite (tshift_tsubst_1 0 (n'' + n')).
rewrite tshift_tshift_prop;apply (IHT2 (S n'')).
Qed.

Lemma tsubst_tsubst_prop:
  forall (n:nat) (T U V:typ),
  (tsubst (tsubst T 0 U) n V) =
  (tsubst (tsubst T (S n) (tshift 0 V)) 0 (tsubst U n V)).
Proof.
intros n T U V.
replace n with (0 + n).
apply tsubst_tsubst;auto.
omega.
Qed.

End M_T_Nat.

(******************************************************************************************)
Import M_T_Nat.

(******************************************************************************************)
(*          Definitions                                                                   *)
(******************************************************************************************)

(*  decidable equality on types  *)
Fixpoint typ_eq (T T':typ) {struct T}:bool:=
  match T, T' with
  | t_var n      , t_var n'     => beq_t_nat n n'
  | top         , top         => true
  | arrow t1 t2 , arrow s1 s2 => typ_eq t1 s1 && typ_eq t2 s2
  | all   t1 t2 , all s1 s2   => typ_eq t1 s1 && typ_eq t2 s2
  | _          , _            => false
end.  

(* lists of types *)
Inductive t_list:Set:=
  | t_nil:t_list
  | t_cons:t_list -> typ -> t_list.

Fixpoint t_length (e:t_list){struct e}:t_nat:=
  match e with
  | t_nil          => t_O
  | t_cons e' T'   => t_S (t_length e')
  end.

(* well-founded indices of lists *)
Fixpoint wf_t_ind (e:t_list) (X:t_nat) {struct e}:bool:=
  match e with
  | t_nil       => false
  | t_cons e' T => if (t_nat_eq_dec X t_O)  then  true else wf_t_ind e' (t_pred X)
  end.

(* well-founded types *)
Fixpoint wf_typ (e:t_list) (T:typ) {struct T}:bool:=
  match T with
  | t_var X      => wf_t_ind e X
  | top         => true
  | arrow T1 T2 => wf_typ e T1 && wf_typ e T2
  | all T1 T2   => wf_typ e T1 && wf_typ (t_cons e T1) T2
  end.

(* well-founded lists of types *)
Fixpoint wf_t_list (e:t_list){struct e}:bool:=
  match e with
    t_nil      => true
  | t_cons e T => wf_typ e T && wf_t_list e
  end.

(* get (shifted) type for given index *)
Fixpoint get_t_list (e:t_list) (X:t_nat){struct e}:typ:=
  match e with
  | t_nil     => top
  | t_cons e' t =>
       tshift t_O (if (t_nat_eq_dec X t_O) then t else get_t_list e' (t_pred X))
  end.

(* types within lists *)
Definition In_t_list (e:t_list) (X:t_nat) (T:typ):=wf_t_ind e X && typ_eq (get_t_list e X) T.

(******************************************************************************************)
(*      Subtyping relation  (undecidable)                                                 *) (******************************************************************************************)

Inductive sub:t_list -> typ -> typ -> Prop:=
  | SA_Top:
      forall (e:t_list) (T:typ), wf_t_list e ->wf_typ e T -> sub e T top
  | SA_Refl_TVar:
     forall (e:t_list)(X:t_nat), wf_t_list e ->  wf_t_ind e X->sub e (t_var X) (t_var X)
  | SA_Trans_TVar:
      forall (e:t_list) (T U:typ) (X:t_nat), In_t_list e X U->sub e U T -> sub e (t_var X) T
  | SA_Arrow:
      forall (e:t_list) (T1 T2 S1 S2:typ),
      sub e T1 S1 -> sub e S2 T2 -> sub e (arrow S1 S2) (arrow T1 T2)
  | SA_All:
      forall (e:t_list) (T1 T2 S1 S2:typ),
      sub e T1 S1 -> sub (t_cons e T1) S2 T2 -> sub e (all S1 S2) (all T1 T2).
(******************************************************************************************)
