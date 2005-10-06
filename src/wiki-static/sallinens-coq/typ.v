(*****************************************)
(*   Submission for PoplMark challenges  *)
(*   Jevgenijs Sallinens, August 2005    *) 
(*      Typing relation (typ.v)          *) 
(*****************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Bool.
Require Import tactics.
Require Import sub_defs.
Require Import typ_defs.
Require Import sub.
Import M_T_Nat.

(******************************************************************************************)
(*      General lemmas                                                                    *) (******************************************************************************************)

Lemma wf_env_bounds:forall (e:env)(T:typ),
   wf_env e -> wf_typ (env_types e) T -> wf_env (ebound e T).
Proof.
simpl;intros;b_auto.
Qed.

Lemma wf_env_vars:forall (e:env)(T:typ),
   wf_env e -> wf_typ (env_types e) T -> wf_env (evar e T).
Proof.
simpl;intros;b_auto.
Qed.

Lemma wf_env_bounds0:forall (e:env)(T:typ),
   wf_env (ebound e T) -> wf_env e.
Proof.
simpl;intros;b_auto.
Qed.

Lemma wf_env_vars0:forall (e:env)(T:typ),
   wf_env (evar e T) -> wf_env e.
Proof.
simpl;intros;b_auto.
Qed.

Lemma wf_env_bounds1:forall (e:env)(T:typ),
   wf_env (ebound e T) -> wf_typ (env_types e) T.
Proof.
simpl;intros;b_auto.
Qed.


Lemma typing_wf1:
  forall (e:env) (t:term) (U:typ),
  typing e t U -> wf_env e.
Proof.
intros e t U H; induction H;intros;auto.
apply wf_env_vars0 with T1;auto.
apply wf_env_bounds0 with T1;auto.
Qed.

Lemma wf_env_vars1:forall (e:env)(T:typ),
   wf_env (evar e T) -> wf_typ (env_types e) T.
Proof.
simpl;intros;b_auto.
Qed.


Lemma wf_v_ind_bound:forall (e:env)(T:typ)(X:t_nat),
   wf_v_ind (ebound e T) X -> wf_v_ind e X.
Proof.
auto.
Qed.

Lemma wf_env_list:forall (e:env),
  wf_env e -> wf_t_list (env_types e). 
Proof.
induction e;simpl;intros;b_auto.
Qed.

Lemma b_t_length:forall (e:env),
  b_length e = t_length (env_types e). 
Proof.
induction e;simpl;intros;b_auto.
rewrite IHe;auto.
Qed.

Lemma env_cons:forall (e:env)(T:typ),
  env_types (ebound e T) = t_cons (env_types e) T. 
Proof.
induction e;simpl;intros;b_auto.
Qed.

Lemma In_env_var_wf:forall (e:env) (X:t_nat) (T:typ),
   In_env_var e X T -> wf_v_ind e X.
Proof.
unfold In_env_var;intros;b_auto.
Qed.

Lemma In_env_var_0_1:forall  (e:env)(T:typ),
   In_env_var (evar e T) t_O T.
Proof.
unfold In_env_var;simpl;b_auto.
case (t_nat_eq_dec t_O t_O);intros;b_auto.
absurd (t_O = t_O);auto.
absurd (t_O = t_O);auto.
Qed.

Lemma In_env_var_0_2:forall (e:env) (T S:typ),
  In_env_var (evar e T) t_O S -> S = T.
Proof.
unfold In_env_var;simpl;b_auto.
case (t_nat_eq_dec t_O t_O);intros;b_auto.
apply typ_eq_eq;auto.
absurd (t_O = t_O);auto.
Qed.

Lemma In_env_var_S_1:forall  (e:env)(T T1:typ)(X:t_nat),
  X <> t_O -> In_env_var e (t_pred X) T1->In_env_var (evar e T) X T1.
Proof.
unfold In_env_var;simpl;intros;b_auto;case (t_nat_eq_dec X t_O);intros;b_auto.
Qed.

Lemma In_env_var_S_2:forall  (e:env)(T T1:typ)(X:t_nat),
  X <> t_O ->
  In_env_var (evar e T) X T1 -> In_env_var e (t_pred X) T1.
Proof.
unfold In_env_var;simpl;intros e T T1 X;case (t_nat_eq_dec X t_O);intros;b_auto.
Qed.

Lemma In_env_var_1:forall  (e:env)(T T1:typ)(X:t_nat),
  In_env_var e X T1 -> In_env_var (ebound e T) X (tshift t_O T1).
Proof.
unfold In_env_var;simpl;intros;b_auto.
rewrite <-(typ_eq_eq H1);auto.
Qed.


Lemma get_In_env_var:forall (e:env) (X:t_nat) ,
   wf_v_ind e X -> In_env_var e X (get_v_env e X).
Proof.
unfold In_env_var;simpl;intros;b_auto.
Qed.

Lemma In_env_var_2:forall  (e:env)(T T1:typ)(X:t_nat),
   In_env_var (ebound e T) X T1 -> T1 = tshift t_O (get_v_env e X).
Proof.
unfold In_env_var;simpl;intros;b_auto.
rewrite <-(typ_eq_eq H1);auto.
Qed.

Lemma In_env_var_3:forall  (e:env)(T1 T2 T:typ)(X:t_nat),
  In_env_var (ebound e T1) X T -> In_env_var (ebound e T2) X T.
Proof.
unfold In_env_var;simpl;intros;b_auto.
Qed.

Lemma In_env_var_eq:forall (e:env) (x:t_nat)(T1 T2:typ),
  In_env_var e x  T1 -> In_env_var e x T2 -> T1 = T2.
Proof.
unfold In_env_var;simpl;intros;b_auto.
rewrite (typ_eq_eq H2);auto.
rewrite (typ_eq_eq H3);auto.
Qed.

Lemma term_eq_eq:forall t1 t2,
   term_eq t1 t2 -> t1 = t2.
Proof.
induction t1;induction t2;simpl;intros;b_auto.
rewrite <-beq_t_nat_eq with t t0;auto.
rewrite TrueEq;auto.
rewrite  IHt1 with t2;auto.
rewrite  (typ_eq_eq H0);auto.
rewrite  IHt1_1 with t2_1;auto.
rewrite  IHt1_2 with t2_2;auto.
rewrite  IHt1 with t2;auto.
rewrite  (typ_eq_eq H0);auto.
rewrite  IHt1 with t2;auto.
rewrite  (typ_eq_eq H1);auto.
Qed.

Lemma term_refl:forall t, term_eq t t.
Proof.
induction t;simpl;intros;b_auto.
rewrite <-beq_t_nat_refl;auto.
Qed.

Hint Resolve term_refl:core.

Lemma term_refl1:forall t (x:bool),
   (term_eq t t -> false) -> x.
Proof.
induction t;simpl;intros;b_auto.
apply Contradiction;apply H;rewrite <-beq_t_nat_refl;auto.
Qed.

(******************************************************************************************)
(*  v_narrow1 is narrowing of v_narrow 2                                                  *)
(******************************************************************************************)


Fixpoint v_narrow1  (e0:env)(M N:typ) (e:env){struct e}:env:=
  match e with
  | empty             => ebound e0 M
  | ebound e' T'      => ebound (v_narrow1 e0 M N e' ) T'
  | evar e' T'        => evar (v_narrow1 e0 M N e') T' 
  end.

Fixpoint v_narrow2 (e0:env) (M N:typ) (e:env){struct e}:env:=
  match e with
  | empty             =>  ebound e0 N
  | ebound e' T'      => ebound (v_narrow2 e0 M N e' ) T'
  | evar e' T'        => evar (v_narrow2 e0 M N e') T' 
  end.

Fixpoint wf_v_narrow (e0:env) (M N:typ) (e:env){struct e}:bool:=
  match e with
  | empty          => true
  | ebound e' T'   => wf_typ (env_types (v_narrow2 e0 M N e'))  T' && wf_v_narrow e0 M N e'
  | evar e' T'     => wf_typ  (env_types (v_narrow2 e0 M N e'))  T' && wf_v_narrow e0 M N e'
  end.

Lemma narrow_1:forall (e e0:env) (M N:typ),
  env_types (v_narrow1 e0 M N e) = narrow1 (env_types e0) M N (env_types e).
Proof.
intros e e0 M N; induction e;simpl;intros;b_auto;simpl.
rewrite IHe;auto.
Qed.

Lemma narrow_2:forall (e e0:env) (M N:typ),
  env_types (v_narrow2 e0 M N e) = narrow2 (env_types e0) M N  (env_types e).
Proof.
intros e e0 M N; induction e;simpl;intros;b_auto;simpl.
rewrite IHe;auto.
Qed.

Lemma wf_narrows:forall (e e0:env) (M N:typ),
  wf_v_narrow e0 M N e ->
  wf_narrow (env_types e0) M N  (env_types e).
intros e e0 M N; induction e;simpl;intros;b_auto;simpl.
rewrite <- narrow_2;auto.
Qed.

Lemma v_narrow_leng:
  forall (e e0:env)(M N:typ),
  t_lengthes (env_types (v_narrow1 e0 M N e))  (env_types  (v_narrow2 e0 M N e)).
Proof.
intros e e0 M N; induction e;simpl;intros;b_auto.
Qed.

Lemma v_narrow_wf_env:
  forall (e e0:env)(M N:typ),
  sub  (env_types e0) N M -> wf_v_narrow e0 M N e -> 
  wf_env (v_narrow1 e0 M N e) -> wf_env (v_narrow2 e0 M N e) .
Proof.
intros e e0 M N H0 H; induction e;simpl in *;intros;b_auto.
apply sub_wf1 with M;auto.
Qed.

Lemma In_env_var_narrow:
 forall (e e0:env)(M N:typ)(X:t_nat)(T:typ),
 In_env_var (v_narrow1 e0 M N e) X T -> In_env_var (v_narrow2 e0 M N e) X T.
Proof.
induction e;intros e0 M N X T.
simpl;intros;apply In_env_var_3 with M;auto.
case  (t_nat_eq_dec X t_O);intro HX.
rewrite HX;auto.
unfold In_env_var;simpl.
case (t_nat_eq_dec t_O t_O);intros;b_auto.
absurd (t_O = t_O);auto.
absurd (t_O = t_O);auto.
simpl;intros;apply In_env_var_S_1;auto.
apply IHe.
apply In_env_var_S_2 with  t; auto.
intros H1;rewrite (In_env_var_2 H1);auto.
simpl;apply In_env_var_1.
apply IHe;auto.
apply get_In_env_var;auto.
apply wf_v_ind_bound with t.
apply In_env_var_wf with T;auto.
Qed.

(******************************************************************************************)
(*  v_insert2 is obtained by inserting type varibles in v_insert1                         *)
(******************************************************************************************)

Fixpoint v_insert1 (e0:env) (T:typ) (e:env){struct e}:env:=
  match e with
  | empty          => e0
  | evar e' T'     => evar (v_insert1 e0 T e' ) T'
  | ebound e' T'   => ebound (v_insert1 e0 T e' ) T'
  end.

Fixpoint v_insert2 (e0:env) (T:typ) (e:env){struct e}:env:=
  match e with
  | empty          => (ebound e0 T)
  | evar e' T'     => evar (v_insert2 e0 T e' ) (tshift (b_length e') T')
  | ebound e' T'   => ebound (v_insert2 e0 T e' ) (tshift (b_length e') T')
  end.

Fixpoint wf_v_insert (e0:env) (T:typ) (e:env){struct e}:bool:=
  match e with
  | empty          => wf_typ (env_types e0) T
  | evar e' T'     => wf_v_insert e0 T e'
  | ebound e' T'   => wf_v_insert e0 T e'
  end.

Lemma insert_1:forall (e e0:env) (T0:typ),
  env_types (v_insert1 e0 T0 e) = insert1 (env_types e0) T0 (env_types e).
Proof.
intros e e0 T0; induction e;simpl;intros;b_auto;simpl.
rewrite IHe;auto.
Qed.

Lemma insert_2:forall (e e0:env) (T0:typ),
   env_types (v_insert2 e0 T0 e) = insert2 (env_types e0) T0 (env_types e).
Proof.
intros e e0 T0; induction e;simpl;intros;b_auto;simpl.
rewrite IHe;rewrite b_t_length;auto.
Qed.

Lemma In_env_var_insert1:
  forall (e e0:env)(T0:typ)(X:t_nat)(T:typ), 
  In_env_var (v_insert1 e0 T0 e) X T -> In_env_var (v_insert2 e0 T0 e) X (tshift (b_length e) T).
Proof.
intros e;induction e;simpl.
intros;apply In_env_var_1;auto.
intros e0 T0 X T;case (t_nat_eq_dec X t_O);intro HX.
rewrite HX.
intros  H;rewrite (In_env_var_0_2 H).
simpl;apply In_env_var_0_1.
intros  H;apply In_env_var_S_1;auto.
apply IHe.
apply In_env_var_S_2 with t;auto.
intros e0 T0 X T H.
rewrite (In_env_var_2 H).
rewrite <-tshift_tshift_prop.
apply In_env_var_1;auto.
apply IHe;auto.
apply get_In_env_var.
apply wf_v_ind_bound with t.
apply In_env_var_wf with T;auto.
Qed.

Lemma v_insert_wf:
  forall (e:env) (T:typ)(e0:env) , 
  wf_typ (env_types e0) T -> wf_env (v_insert1 e0 T e) ->
  wf_env (v_insert2 e0 T e). 
Proof.
intros e;induction e; simpl;intros;b_auto.
rewrite  insert_2.
rewrite b_t_length;auto.
apply insert_wf_typ;auto.
rewrite <- insert_1;auto.
rewrite  insert_2.
rewrite b_t_length;auto.
apply insert_wf_typ;auto.
rewrite <- insert_1;auto.
Qed.

(******************************************************************************************)
(*      Weakening  lemmas  (A4, A5, A6)                                                   *) (******************************************************************************************)

Lemma typing_weakening_bound_ind:
  forall (e:env)(t:term) (U:typ),
  typing e t U ->  
  forall (e0 e1:env)(T0:typ), 
  wf_typ (env_types e0) T0 -> e = v_insert1 e0 T0 e1 ->
  typing (v_insert2 e0 T0 e1) (shift_typ (b_length e1) t) (tshift (b_length e1) U).
Proof.
intros  e t U H.
induction H;simpl;intros;auto.
apply T_Var.
apply v_insert_wf;auto.
rewrite <-H2;auto.
apply In_env_var_insert1;auto.
rewrite <-H2;auto.
apply T_Abs.
replace (b_length e1) with (b_length (evar e1 T1));auto. 
apply IHtyping with (e1:=(evar e1 T1))(e0:=e0)(T0:=T0);auto.
rewrite H1;auto.
apply T_App with (tshift (b_length e1) T11);simpl in *;auto.
apply T_Tabs;auto.
replace (t_S (b_length e1)) with (b_length (ebound e1 T1));auto. 
apply IHtyping with (e1:=(ebound e1 T1))(e0:=e0)(T0:=T0);auto.
rewrite H1;auto.
rewrite (tshift_tsubst_prop_2 (b_length e1)).
apply T_Tapp  with (tshift  (b_length e1) T11);simpl in *;auto.
rewrite  insert_2.
rewrite b_t_length;auto.
apply sub_weakening_ind with  (env_types e);auto.
rewrite H2;auto.
apply insert_1.
apply T_Sub with (tshift (b_length e1) T1);auto.
rewrite  insert_2.
rewrite b_t_length;auto.
apply sub_weakening_ind with (env_types e);auto.
rewrite H2;auto.
apply insert_1.
Qed.

(******************************************************************************************)

Lemma typing_weakening_bound0:
  forall (e:env) (t:term) (U V:typ),
  wf_typ (env_types e) V -> typing e t U ->
  typing (ebound e V) (shift_typ t_O t) (tshift t_O U).
Proof.
intros e t U V H0 H.
apply typing_weakening_bound_ind with (e:=e)(e0:=e)(e1:=empty)(T0:=V);auto.
Qed.

(******************************************************************************************)
(*  insert_var2 is obtained by inserting varibles in insert_var1                          *)
(******************************************************************************************)

Fixpoint insert_var1 (e0:env) (T:typ) (e:env){struct e}:env:=
  match e with
  | empty          => e0
  | evar e' T'     => evar (insert_var1 e0 T e' ) T'
  | ebound e' T'   => ebound (insert_var1 e0 T e' ) T'
  end.

Fixpoint insert_var2 (e0:env) (T:typ) (e:env){struct e}:env:=
  match e with
  | empty          => evar e0 T
  | evar e' T'     => evar (insert_var2 e0 T e' ) T'
  | ebound e' T'   => ebound (insert_var2 e0 T e' )  T'
  end.

Fixpoint wf_insert_var (e0:env) (T:typ) (e:env){struct e}:bool:=
  match e with
  | empty          => wf_typ (env_types e0) T
  | evar e' T'     => wf_insert_var e0 T e'
  | ebound e' T'   => wf_insert_var e0 T e'
  end.

Lemma In_env_var_insert_0:
  forall (X:t_nat) (e0:env) (T0 T:typ),
  In_env_var e0 X T -> In_env_var (evar e0 T0) (t_semi_S t_O X) T.
Proof.
intros;rewrite t_semi_S_0_n;apply In_env_var_S_1;auto.
apply t_O_S;auto.
rewrite  t_pred_Sn;auto.
Qed.

Lemma In_env_var_insert_var:
  forall (e:env)(X:t_nat)(e0:env)(T0 T:typ), 
  In_env_var (insert_var1 e0 T0 e) X T ->
  In_env_var (insert_var2 e0 T0 e) (t_semi_S (v_length e) X) T.
Proof.
intros e;induction e;simpl.
apply In_env_var_insert_0;auto.
intros X;case (t_nat_eq_dec  X  t_O);intros HX.
rewrite HX;intros.
rewrite (In_env_var_0_2 H).
rewrite t_semi_S_S_0;auto.
apply In_env_var_0_1.
intros;apply In_env_var_S_1;auto.
apply t_semi_S_3;auto.
rewrite t_semi_S_1;auto.
apply IHe;auto.
apply In_env_var_S_2 with t;auto.
intros;rewrite In_env_var_2 with (insert_var1 e0 T0 e) t T X;auto.
apply In_env_var_1.
apply IHe;auto.
apply get_In_env_var.
apply wf_v_ind_bound with t.
apply In_env_var_wf with T;auto.
Qed.

Lemma In_env_var_insert_20:
  forall (X:t_nat) (e0:env) (T0 T:typ),
  In_env_var (evar e0 T0) (t_semi_S t_O X) T -> In_env_var e0 X T.
Proof.
intros X e0 T0 T.
rewrite t_semi_S_0_n;auto.
intros;rewrite <- t_pred_Sn with X.
intros;apply In_env_var_S_2 with T0;auto.
apply t_O_S;auto.
Qed.

Lemma In_env_var_insert_var2:
  forall (e:env) (X:t_nat)(e0:env)(T0 T:typ),
  In_env_var (insert_var2 e0 T0 e) (t_semi_S (v_length e) X) T ->
  In_env_var (insert_var1 e0 T0 e) X T.
Proof.
intros  e; induction e;simpl.
apply In_env_var_insert_20;auto.
intros X;case (t_nat_eq_dec  X  t_O);intros HX.
rewrite HX;rewrite t_semi_S_S_0;auto.
unfold In_env_var;simpl.
case (t_nat_eq_dec t_O t_O);intros;b_auto.
absurd (t_O = t_O);auto.
absurd (t_O = t_O);auto.
intros;apply In_env_var_S_1;auto.
apply IHe;auto.
rewrite <-t_semi_S_1;auto.
apply In_env_var_S_2 with t;auto.
apply t_semi_S_3;auto.
intros X e0 T0 T H;
rewrite In_env_var_2 with (insert_var2 e0 T0 e) t T (t_semi_S (v_length e) X);auto.
intros.
apply In_env_var_1.
apply IHe;auto.
apply get_In_env_var.
apply wf_v_ind_bound with t.
apply In_env_var_wf with T;auto.
Qed.

Lemma insert_var_le1:
  forall (e e0:env) (T0:typ),
  t_list_le (env_types (insert_var2 e0 T0 e)) 
  (env_types (insert_var1 e0 T0 e)).
Proof.
intros e;induction e; simpl;intros;b_auto.
Qed.

Lemma insert_var_le2:
  forall (e e0:env) (T0:typ),
  t_list_le (env_types (insert_var1 e0 T0 e))
  (env_types (insert_var2 e0 T0 e)).
Proof.
intros e;induction e; simpl;intros;b_auto.
Qed.

Lemma insert_var_wf_env:
  forall (e:env) (T0:typ)(e0:env) , 
  wf_insert_var e0 T0 e ->wf_env (insert_var2 e0 T0 e)->
  wf_env (insert_var1 e0 T0 e). 
Proof.
intros e;induction e; simpl;intros;b_auto.
apply wf_typ_leng with  (env_types (insert_var2 e0 T0 e));auto.
apply t_list_le_leng.
apply insert_var_le1;auto.
apply wf_typ_leng with  (env_types (insert_var2 e0 T0 e));auto.
apply t_list_le_leng.
apply insert_var_le1;auto.
Qed.


Lemma typing_weakening_var_ind:
  forall (e:env)(t:term) (U:typ),
  typing e t U ->  
  forall (e0 e1:env)(T0:typ), 
  wf_insert_var e0 T0 e1 -> e =  (insert_var1 e0 T0 e1) ->
  wf_env (insert_var2 e0 T0 e1) ->
  typing (insert_var2 e0 T0 e1) (shift (v_length e1) t)  U.
intros t U e H;induction H;simpl;intros;auto.
apply T_Var; auto.
apply  In_env_var_insert_var;auto.
rewrite <-H2;auto.
apply T_Abs.
replace (t_S (v_length e1)) with (v_length (evar e1 T1));auto.
apply IHtyping with (e1:=(evar e1 T1))(e0:=e0)(T0:=T0);simpl;b_auto.
rewrite H1;auto.
apply wf_typ_leng with 
(env_types  (insert_var1 e0 T0 e1));auto.
apply t_list_le_leng.
apply insert_var_le2;auto.
rewrite <- H1;auto.
apply wf_env_vars1;auto.
apply (typing_wf1 H);auto.
apply T_App with T11;auto.
apply T_Tabs.
replace (v_length e1) with (v_length (ebound e1 T1));auto.
apply IHtyping with (e1:=(ebound e1 T1))(e0:=e0)(T0:=T0);simpl;b_auto.
rewrite H1;auto.
apply wf_typ_leng with 
(env_types  (insert_var1 e0 T0 e1));auto.
apply t_list_le_leng.
apply insert_var_le2;auto.
rewrite <- H1;auto.
apply wf_env_bounds1;auto.
apply (typing_wf1 H);auto.
apply T_Tapp with T11;auto.
apply sub_extensionality with  (env_types (insert_var1 e0 T0 e1)); auto.
rewrite <- H2;auto.
apply insert_var_le2;auto.
apply wf_env_list;auto.
apply T_Sub with T1;auto.
apply sub_extensionality with  (env_types (insert_var1 e0 T0 e1)); auto.
rewrite <- H2;auto.
apply insert_var_le2;auto.
apply wf_env_list;auto.
Qed.

Lemma typing_weakening_var:
  forall (e:env) (t:term) (U V:typ),
  wf_typ  (env_types e) V -> typing  e t U -> typing (evar e V) (shift t_O t) U.
Proof.
intros e;intros.
apply  typing_weakening_var_ind  with (e:=e)(e0:=e)(e1:=empty)(T0:=V);auto.
simpl;b_auto.
apply (typing_wf1 H0).
Qed.

Lemma typing_weakening_bound:
  forall (e0 e:env)(T0:typ) (t:term) (U V T1 T2:typ),
  wf_typ (env_types (insert_var2 e0 T0 e)) V ->
  In_env_var (insert_var1 e0 T0 e) (v_length e) T1 ->
  typing  (insert_var2 e0 T0 e) t (tshift t_O T1)  ->
  In_env_var (ebound (insert_var1 e0 T0 e) V) (v_length e) T2 -> 
  typing  (ebound (insert_var2 e0 T0 e) V) (shift_typ t_O t) (tshift t_O T2) .
Proof.
intros e0 e T0 t U V T1 T2;intros.
cut (TRUE (In_env_var (ebound (insert_var1 e0 T0 e) V) (v_length e)  (tshift t_O T1))).
intros HX.
rewrite  (In_env_var_eq H2 HX).
apply typing_weakening_bound0;auto.
apply In_env_var_1;auto.
Qed.

(******************************************************************************************)
(*             Substitution preserves typing (Lemma A.8)                                  *)
(******************************************************************************************)

Opaque wf_env.

Lemma subst_preserves_typing0:
  forall (e:env)(t:term) (U:typ),  typing e t U ->  
  forall (e0 e1:env)(T0 T:typ)(u:term), 
  e = insert_var2 e0 T0 e1 -> wf_insert_var e0 T0 e1 -> 
  In_env_var e (v_length e1) T -> typing (insert_var1 e0 T0 e1) u T -> 
  typing (insert_var1 e0 T0 e1) (subst t (v_length e1) u) U.
Proof.
intros e t U H;induction H;unfold In_env_var;simpl;intros.
simpl;case (t_nat_eq_dec x (v_length e1));intros HX.
rewrite HX in H0;rewrite  (In_env_var_eq H0 H3);auto.
apply T_Var.
apply typing_wf1 with u  T1;auto.
apply In_env_var_insert_var2; auto.
rewrite <-H1;auto.
rewrite t_semi_S_P;auto.
apply T_Abs.
replace (t_S (v_length e1)) with  (v_length (evar e1 T1));auto.
apply IHtyping with (e1:=(evar e1 T1))(e0:=e0)(T0:=T0)(T:=T);auto.
simpl;rewrite H0;simpl;auto.
unfold In_env_var;simpl;intros;b_auto.
case (t_nat_eq_dec (t_S (v_length e1)) t_O);intros;b_auto.
rewrite  t_pred_Sn;auto.
case (t_nat_eq_dec (t_S (v_length e1)) t_O);intros;b_auto.
absurd (t_S (v_length e1) = t_O);auto.
apply t_O_S.
rewrite  t_pred_Sn;auto.
apply typing_weakening_var with (e:=insert_var1 e0 T0 e1)(t:=u)(U:=T)(V:=T1);auto.
apply wf_env_vars1.
simpl.
apply insert_var_wf_env  with (e:=(evar e1 T1))(e0:=e0)(T0:=T0);auto.
simpl;rewrite <-H0;apply typing_wf1 with t T2;auto.
apply T_App with T11;auto.
apply IHtyping1 with T;auto.
apply IHtyping2 with T;auto.
apply T_Tabs;auto.
replace  (v_length e1) with  (v_length (ebound e1 T1));auto.
apply IHtyping with   (e1:=(ebound e1 T1))(e0:=e0)(T0:=T0)(T:=tshift t_O T);auto.
rewrite H0;auto.
apply In_env_var_1;auto.
apply typing_weakening_bound0 with (e:=insert_var1 e0 T0 e1)(t:=u)(U:=T)(V:=T1);auto.
apply wf_env_bounds1.
apply insert_var_wf_env with (e:=(ebound e1 T1))(e0:=e0)(T0:=T0);auto.
simpl;rewrite <-H0;auto.
apply typing_wf1 with t T2;auto.
apply T_Tapp with T11;auto.
apply IHtyping with T;auto.
apply sub_extensionality with (env_types (insert_var2 e0 T0 e1)); auto.
rewrite <- H1;auto.
apply insert_var_le1;auto.
apply wf_env_list;auto.
apply (typing_wf1 H4).
simpl;apply T_Sub with T1;auto.
apply IHtyping with T;auto.
apply sub_extensionality with (env_types (insert_var2 e0 T0 e1)); auto.
rewrite <- H1;auto.
apply insert_var_le1;auto.
apply wf_env_list;auto.
apply (typing_wf1 H4).
Qed.

Transparent wf_env.

Lemma subst_preserves_typing:
  forall (e:env) (t:term) (V:typ)(t1:typ),
  typing (evar e t1) t V -> forall (u:term),
  typing e u t1 -> typing e (subst t t_O u) V.
Proof.
intros e t V t1 H1 u H2.
apply subst_preserves_typing0 with 
 (e:=(evar e t1))(e0:=e)(e1:=empty)(T0:=t1)(T:=t1);simpl;auto. 
apply  wf_env_vars1;auto.
apply typing_wf1 with t  V;auto.
apply In_env_var_0_1;auto.
Qed.

(******************************************************************************************)
(*  Substitutions in enviroments                                                          *)
(******************************************************************************************)

Fixpoint env_subst0  (e0:env)(M N:typ) (e:env){struct e}:typ:=
  match e with
  | empty         => N
  | ebound e' T'  => tshift t_O  (env_subst0 e0 M N e')
  | evar e' T'    => env_subst0 e0 M N e'
  end.

Fixpoint env_subst3  (e0:env)(M N:typ) (e:env){struct e}:env:=
  match e with
  | empty         => empty
  | ebound e' T'  => ebound (env_subst3 e0 M N e') T'
  | evar e' T'    => env_subst3 e0 M N e'
  end.

Fixpoint env_subst1  (e0:env)(M N:typ) (e:env){struct e}:env:=
  match e with
  | empty         => ebound e0 M
  | ebound e' T'  => ebound (env_subst1 e0 M N e') T'
  | evar e' T'    => evar (env_subst1 e0 M N e') T'
  end.

Fixpoint env_subst2  (e0:env)(M N:typ) (e:env){struct e}:env:=
  match e with
  | empty         => e0
  | ebound e' T'  => ebound (env_subst2 e0 M N e') (tsubst T' (b_length (env_subst3 e0 M N e'))
                    (env_subst0 e0 M N e'))
  | evar e' T'    => evar (env_subst2 e0 M N e') (tsubst T' (b_length (env_subst3 e0 M N e'))
                    (env_subst0 e0 M N e'))
 end.

Fixpoint wf_env_subst (e0:env) (M N:typ) (e:env){struct e}:bool:=
  match e with
  | empty         => wf_typ (env_types e0) M
  | ebound e' T'  => wf_env_subst e0 M N e' && wf_typ  (env_types (env_subst1 e0 M N e')) T'
  | evar e' T'    => wf_env_subst e0 M N e' && wf_typ  (env_types (env_subst1 e0 M N e')) T'
  end.

Lemma env_subst_wf_typ_0:
  forall (e e0:env)(M N:typ),
  sub (env_types e0) N M -> wf_env_subst e0 M N e -> 
  wf_t_list (env_types (env_subst2 e0 M N e)) ->
  wf_typ (env_types (env_subst2 e0 M N e)) (env_subst0 e0 M N e).
Proof.
intros e e0 M N; induction e.
simpl;intros;b_auto.
apply sub_wf1 with M;auto.
simpl;intros;apply IHe;b_auto.
simpl;intros;apply wf_typ_weakening;b_auto.
Qed.

Lemma env_subst_wf_t_ind:
  forall (e e0:env)(M N:typ),
  forall (X:t_nat), 
  wf_t_ind  (env_types (env_subst1 e0 M N e)) (t_semi_S (b_length (env_subst3 e0 M N e) ) X) ->
  wf_t_ind  (env_types (env_subst2 e0 M N e)) X.
Proof.
intros e e0 M N; induction e;auto;intros X;simpl.
rewrite t_semi_S_0_n.
case (t_nat_eq_dec (t_S X) t_O);auto.
intros;absurd(t_S X = t_O);auto.
apply t_O_S.
rewrite t_pred_Sn;auto.
case (t_nat_eq_dec X t_O);intros HX.
rewrite HX;intros;b_auto.
case (t_nat_eq_dec (t_semi_S (t_S (b_length (env_subst3 e0 M N e))) X) t_O);auto.
intros;absurd (t_semi_S (t_S (b_length (env_subst3 e0 M N e))) X = t_O);auto.
apply t_semi_S_3;auto.
rewrite t_semi_S_1;auto.
Qed.

Lemma env_subst_wf_typ1:
  forall (U:typ)(e:env),  wf_typ  (env_types e) U ->
  forall (e1 e0:env)(M N:typ),
  e =env_subst1 e0 M N e1 -> sub  (env_types e0) N M -> wf_env_subst e0 M N e1->
  wf_t_list (env_types (env_subst2 e0 M N e1)) ->
  wf_typ  (env_types (env_subst2 e0 M N e1))  
  (tsubst U  (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1)).
Proof.
intros U;induction U;simpl;intros;b_auto.
case (t_nat_eq_dec t (b_length (env_subst3 e0 M N e1)));intros.
apply env_subst_wf_typ_0;auto.
simpl;apply env_subst_wf_t_ind;auto.
rewrite t_semi_S_P;auto.
rewrite <-H0;auto.
replace (t_S (b_length (env_subst3 e0 M N e1))) with 
(b_length (env_subst3 e0 M N (ebound e1 U1)));auto.
rewrite <- env_cons.
apply IHU2 with (e:=(ebound e U1)) 
(e1:=ebound e1 U1)(e0:=e0)(M:=M)(N:=N); simpl;b_auto.
rewrite <-H0;auto.
rewrite <-H0;auto.
Qed.

Lemma env_subst_wf_t_list:
  forall (e e0:env)(M N:typ),
  sub  (env_types e0) N M -> wf_env_subst e0 M N e ->
  wf_t_list (env_types (env_subst2 e0 M N e)). 
Proof.
intros e e0 M N; induction e;simpl;intros;b_auto.
apply sub_wf0 with N M;auto.
apply env_subst_wf_typ1 with (env_subst1 e0 M N e);b_auto.
Qed.

Lemma env_subst_wf_env:
  forall (e e0:env)(M N:typ),
  sub  (env_types e0) N M -> wf_env (env_subst1 e0 M N e) -> wf_env_subst e0 M N e->
  wf_env (env_subst2 e0 M N e). 
Proof.
intros e e0 M N; induction e;simpl;intros;b_auto.
apply env_subst_wf_typ1 with (env_subst1 e0 M N e);b_auto.
apply env_subst_wf_t_list;auto.
apply env_subst_wf_typ1 with (env_subst1 e0 M N e);b_auto.
apply env_subst_wf_t_list;auto.
Qed.

Lemma env_subst_wf_typ2:
   forall (e e0:env)(M N U:typ),
   sub  (env_types e0) N M -> wf_env_subst e0 M N e ->
   wf_typ  (env_types (env_subst1 e0 M N e)) U ->
   wf_typ  (env_types (env_subst2 e0 M N e)) (tsubst U  (b_length (env_subst3 e0 M N e )) (env_subst0 e0 M N e) ).
Proof.
intros e0 e M N U;intros.
apply env_subst_wf_typ1 with (env_subst1 e M N e0);auto.
apply env_subst_wf_t_list;auto.
Qed.

Lemma In_tsubst:
  forall (e:env)(X:t_nat)(T T0 T1 T2:typ),
  In_t_list  (env_types (ebound e T)) (t_semi_S t_O X) T1 ->
  In_t_list  (env_types e) X (tsubst T1 t_O T2).
Proof.
intros e X T T0 T1 T2;rewrite t_semi_S_0_n.
intros H;rewrite  In_t_list_S_2 with  (env_types e) T T1 (t_S X);auto.
rewrite <-tsubst_tshift_prop.
rewrite t_pred_Sn;apply get_In_t_list.
apply wf_t_ind_prop3 with T.
apply In_t_list_wf with T1;auto.
apply t_O_S.
Qed.

Lemma In_env_subst:
  forall (e e0:env)(M N:typ),
  sub  (env_types e0) N M ->wf_env_subst e0 M N e ->
  forall (X:t_nat)(T1:typ), 
  In_t_list   (env_types (env_subst1 e0 M N e)) (t_semi_S (b_length  (env_subst3 e0 M N e)) X) T1 -> 
  In_t_list  (env_types (env_subst2 e0 M N e)) X 
  (tsubst T1 (b_length (env_subst3 e0 M N e)) (env_subst0 e0 M N e)).
Proof.
intros e e0 M N; induction e;simpl.
intros;apply In_tsubst with M;auto.
intros;simpl;apply IHe;b_auto.
intros HA HB;simpl;b_auto.
intros X T1;case (t_nat_eq_dec  X  t_O);intros HX.
rewrite HX;rewrite t_semi_S_S_0;intros H1.
rewrite  (In_t_list_0_2 H1);auto.
rewrite <-tshift_tsubst_prop_1.
apply In_t_list_0_1.
rewrite t_semi_S_2;intros H1;b_auto.
rewrite  In_t_list_S_2 with  (env_types (env_subst1 e0 M N e)) t T1
       (t_S (t_semi_S (b_length (env_subst3 e0 M N e)) (t_pred X)));auto.
rewrite <-tshift_tsubst_prop_1.
apply In_t_list_S_1;auto.
rewrite t_pred_Sn;auto.
apply IHe;b_auto.
apply get_In_t_list.
apply wf_t_ind_prop3 with t.
apply In_t_list_wf with T1;auto.
rewrite <-t_semi_S_1 in H1;auto.
rewrite t_S_pred in H1;auto.
apply t_O_S.
apply t_semi_S_3;auto.
Qed.

Lemma env_subst_sub:
  forall (e e0:env)(M N:typ),
  sub (env_types e0) N M -> wf_env_subst e0 M N e ->
  forall (U:typ), 
  In_t_list (env_types (env_subst1 e0 M N e))  (b_length (env_subst3 e0 M N e)) U ->
  (sub (env_types (env_subst2 e0 M N e)) (env_subst0 e0 M N e) 
  (tsubst U (b_length (env_subst3 e0 M N e)) (env_subst0 e0 M N e))).
Proof.
intros e e0 M N;  induction e;simpl;intros;auto.
rewrite  (In_t_list_0_2 H1).
rewrite <- tsubst_tshift_prop; b_auto.
intros;simpl.
apply IHe;b_auto.
rewrite  In_t_list_S_2 with  (env_types (env_subst1 e0 M N e)) t U
       (t_S (b_length (env_subst3 e0 M N e)));auto.
rewrite <- tshift_tsubst_prop_1.
apply sub_weakening_ind  with 
(e:= (env_types (env_subst2 e0 M N e)))
(e0:= (env_types (env_subst2 e0 M N e)))
(e1:=t_nil)
(T0:= (tsubst  t  (b_length (env_subst3 e0 M N e)) (env_subst0 e0 M N e)));auto.
apply IHe;b_auto.
rewrite t_pred_Sn;auto.
apply get_In_t_list;auto.
apply wf_t_ind_prop3 with t;auto.
apply In_t_list_wf with U;auto.
apply env_subst_wf_typ2;b_auto.
apply t_O_S.
Qed.

Lemma In_env_var_es:
  forall (e e0:env)(M N U:typ)(n:t_nat),
  In_env_var (env_subst1 e0 M N e) n U ->
  In_env_var (env_subst2 e0 M N e) n 
  (tsubst U (b_length  (env_subst3 e0 M N e)) (env_subst0 e0 M N e)).
Proof.
intros e e0 M N; induction e;simpl.
intros;rewrite (In_env_var_2 H);auto.
rewrite<- tsubst_tshift_prop;auto.
apply get_In_env_var;auto.
apply wf_v_ind_bound with M.
apply In_env_var_wf with U;auto.
intros U n;case (t_nat_eq_dec n t_O); intros HX.
rewrite HX.
intros H;rewrite <- (In_env_var_0_2 H).
apply In_env_var_0_1;auto.
intros;apply In_env_var_S_1;b_auto.
apply IHe; b_auto.
apply In_env_var_S_2 with t;auto.
intros U n H;rewrite  (In_env_var_2 H).
rewrite <-(tshift_tsubst_prop_1 (b_length (env_subst3 e0 M N e))).
apply In_env_var_1;auto.
apply IHe; b_auto.
apply get_In_env_var;auto.
apply wf_v_ind_bound with t.
apply In_env_var_wf with U;auto.
Qed.
 
 

(******************************************************************************************)
(*             Type substitution preserves subtyping (Lemma A.10)                         *)
(******************************************************************************************)
 
Lemma tsubst_preserves_subtyping:
  forall (e:t_list) (U V:typ),
  sub  e U V -> 
  forall (e1 e0:env)(M N:typ), 
  e = env_types (env_subst1 e0 M N e1) -> sub  (env_types e0) N M -> 
  wf_env_subst e0 M N e1 ->
  sub  (env_types (env_subst2 e0 M N e1))
  (tsubst U (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1)) 
  (tsubst V (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1)).
Proof.
intros e  U V H; induction H;intros;auto.
apply SA_Top.
apply env_subst_wf_t_list;auto.
apply env_subst_wf_typ2;auto.
rewrite <-H1;auto.
apply sub_reflexivity;auto.
apply env_subst_wf_t_list;auto.
apply env_subst_wf_typ2;auto.
rewrite <-H1;auto.
simpl;case (t_nat_eq_dec X  (b_length (env_subst3 e0 M N e1)) );intros.
apply sub_transitivity with 
 (tsubst U (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1));auto.
apply env_subst_sub;auto.
rewrite <- e2;auto.
rewrite <-H1;auto.
apply SA_Trans_TVar with (tsubst U (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1));auto.
apply In_env_subst;auto.
rewrite t_semi_S_P;auto.
rewrite <-H1;auto.
simpl;apply SA_Arrow; auto.
simpl;apply SA_All; auto.
replace (t_S (b_length  (env_subst3 e0 M N e1))) with 
(b_length (env_subst3 e0 M N (ebound e1 T1)));auto.
rewrite <-env_cons.
apply IHsub2 with (e1:=ebound e1 T1)(e0:=e0)(M:=M)(N:=N);simpl;b_auto.
rewrite <-H1;auto.
rewrite <-H1;apply (sub_wf1 H).
Qed.

(******************************************************************************************)
(*  Well-foundeness lemmas                                                                *)
(******************************************************************************************)

Lemma tsubst_wf_typ:forall (e:env) (U T T1:typ), 
  wf_typ (env_types  (ebound e U)) T1 -> wf_env e ->
  sub (env_types e) T U -> wf_typ (env_types e) (tsubst T1 t_O T).
Proof.
intros.
replace t_O with  (b_length empty) ;auto.
apply env_subst_wf_typ2 with (e0:=e)(M:=U)(N:=T)(U:=T1)(e:=empty);auto.
b_auto.
apply (sub_wf2 H1).
Qed.

Lemma In_env_var_wf_typ:forall (e:env),
   wf_env e -> forall (n:t_nat)(T:typ),In_env_var e n T -> wf_typ (env_types e) T.
Proof.
intros e;induction e;simpl;intros;b_auto.
apply Contradiction;auto.
case (t_nat_eq_dec n t_O);intros HX.
rewrite HX in H0.
rewrite (In_env_var_0_2 H0);auto.
apply H with (t_pred n).
apply In_env_var_S_2 with t;auto.
rewrite (In_env_var_2 H0).
apply wf_typ_weakening;auto.
apply H with n.
apply get_In_env_var.
apply wf_v_ind_bound with t.
apply In_env_var_wf with T;auto.
Qed.


Lemma typing_wf2:forall (e:env) (t:term) (U:typ),
  typing e t U -> wf_typ  (env_types e) U.
Proof.
intros e t U H; induction H;simpl in *;intros;b_auto.
apply In_env_var_wf_typ with x;auto.
apply wf_env_vars1.
apply typing_wf1 with t T2;auto.
apply wf_env_bounds1.
apply typing_wf1 with t T2;auto.
apply tsubst_wf_typ with T11;auto.
apply typing_wf1 with t1 (all  T11 T12);auto.
apply sub_wf2 with (T:=T1);auto.
Qed.


Lemma typing_wf3:forall (e:env) (t:term) (U:typ),
  typing e t U -> wf_term e t.
Proof.
intros e t U H; induction H;simpl in *;intros;b_auto.
apply In_env_var_wf with T;auto.
apply wf_env_vars1;auto.
apply typing_wf1 with t T2;auto.
apply wf_env_bounds1;auto.
apply typing_wf1 with t T2;auto.
apply sub_wf1 with (U:=T11);auto.
Qed.

(******************************************************************************************)
(*           Type substitution preserves typing (Lemma A.11)                              *)
(******************************************************************************************)

Lemma subst_typ_preserves_typing_ind:
 forall (e:env) (t:term) (U:typ),
 typing e t U ->
 forall (e1 e0:env)(M N:typ), 
 e = env_subst1 e0 M N e1 -> sub  (env_types e0) N M -> wf_env_subst e0 M N e1 ->
 typing (env_subst2 e0 M N e1) (subst_typ  t (b_length (env_subst3 e0 M N e1))(env_subst0 e0 M N e1)) 
 (tsubst U (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1)).
Proof.
intros e t U H2;induction H2.
simpl;intros;apply T_Var.
apply env_subst_wf_env;auto.
rewrite <-H1;auto.
apply In_env_var_es;auto.
rewrite <-H1;auto.
simpl;intros;apply T_Abs.
apply IHtyping with (e1:=(evar e1 T1))(e0:= e0)(M:= M)( N:=N);auto.
simpl;rewrite <-H;auto.
simpl;rewrite <-H;b_auto.
apply wf_env_vars1.
apply typing_wf1 with t T2;auto.
simpl;intros;apply T_App with (tsubst T11 (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1)) .
simpl in *;apply IHtyping1;auto.
apply IHtyping2;auto.
simpl;intros;apply T_Tabs.
replace (t_S (b_length (env_subst3 e0 M N e1))) with (b_length (env_subst3 e0 M N (ebound e1 T1)));auto.
apply IHtyping with (e1:=(ebound e1 T1))(e0:= e0)(M:= M)( N:=N);auto.
simpl;rewrite <-H;auto.
simpl;rewrite <-H;b_auto.
apply wf_env_bounds1.
apply typing_wf1 with t T2;auto.
simpl;intros;rewrite (tsubst_tsubst_prop (b_length (env_subst3 e0 M N e1)) ).
apply T_Tapp with (tsubst T11 (b_length (env_subst3 e0 M N e1))  (env_subst0 e0 M N e1));auto.
simpl in *;apply IHtyping;auto.
apply tsubst_preserves_subtyping with  (env_types e);auto.
rewrite <-H0;auto.
simpl;intros;apply T_Sub with (tsubst T1 (b_length (env_subst3 e0 M N e1)) (env_subst0 e0 M N e1)) .
apply IHtyping;auto.
apply tsubst_preserves_subtyping with  (env_types e);auto.
rewrite <-H0;auto.
Qed.

Lemma subst_typ_preserves_typing:forall (e:env) (t:term) (U P Q:typ),
  typing (ebound e Q) t U -> sub  (env_types e) P Q ->
  typing e (subst_typ t t_O P) (tsubst U t_O P).
Proof.
intros e t U P Q H1 H2;intros.
replace t_O with  (b_length empty);auto.
apply subst_typ_preserves_typing_ind with (e:=(ebound e Q))(e0:=e)(M:=Q)(N:=P)(U:=U)(e1:=empty);auto.
b_auto.
apply (sub_wf2 H2);auto.
Qed.

(******************************************************************************************)

