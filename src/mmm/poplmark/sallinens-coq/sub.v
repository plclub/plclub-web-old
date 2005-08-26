(*****************************************)
(*   Submission for PoplMark challenges  *)
(*   Jevgenijs Sallinens, August 2005    *) 
(*      Subtyping relation (sub.v)       *) 
(*****************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import sub_defs.
Require Import tactics.
Require Import Bool.
Require Import Arith.
Import M_T_Nat.

(******************************************************************************************)
(*      General lemmas                                                                    *) (******************************************************************************************)

Lemma typ_eq_eq:forall t1 t2, typ_eq t1 t2 -> t1 = t2.
Proof.
induction t1;induction t2;simpl;intros;b_auto.
rewrite <-beq_t_nat_eq with t t0;auto.
rewrite TrueEq;auto.
rewrite  IHt1_1 with t2_1;auto.
rewrite  IHt1_2 with t2_2;auto.
rewrite  IHt1_1 with t2_1;auto.
rewrite  IHt1_2 with t2_2;auto.
Qed.

Lemma typ_refl:forall t, typ_eq t t.
Proof.
induction t;simpl;intros;b_auto.
rewrite <-beq_t_nat_refl;auto.
Qed.

Hint Resolve typ_refl:core.

Lemma typ_refl1:forall t (x:bool), (typ_eq t t -> false) -> x.
Proof.		
induction t;simpl;intros;b_auto.
apply Contradiction;apply H;rewrite <-beq_t_nat_refl;auto.
apply Contradiction;apply H;auto.
Qed.

Lemma wf_t_ind_prop1:forall  (e:t_list)(T:typ)(X:t_nat),
  X <> t_O -> wf_t_ind e (t_pred X) -> wf_t_ind (t_cons e T) X.
Proof.
simpl;intros;case (t_nat_eq_dec X t_O);auto.
Qed.

Lemma wf_t_ind_prop2:forall  (e:t_list)(T:typ)(X:t_nat), 
  X <> t_O -> wf_t_ind (t_cons e T) X -> wf_t_ind e (t_pred X).
Proof.
simpl;intros e T X;case (t_nat_eq_dec X t_O);intros;b_auto.
Qed.

Lemma wf_t_ind_prop3:forall  (e:t_list)(T:typ)(X:t_nat),
  wf_t_ind (t_cons e T) (t_S X) -> wf_t_ind e X.
Proof.
simpl;intros e T X;case (t_nat_eq_dec X t_O);
case (t_nat_eq_dec (t_S X)t_O);intros;b_auto.
absurd (t_S X = t_O);auto.
apply t_O_S;auto.
rewrite t_pred_Sn in H;auto.
absurd (t_S X = t_O);auto.
apply t_O_S;auto.
rewrite t_pred_Sn in H;auto.
Qed.

Lemma In_t_list_wf:forall (e:t_list) (X:t_nat) (T:typ),
  In_t_list e X T -> wf_t_ind e X.
Proof.
unfold In_t_list;intros;b_auto.
Qed.

Lemma get_In_t_list:forall (e:t_list) (X:t_nat) ,
  wf_t_ind e  X -> In_t_list e X (get_t_list e X).
Proof.
unfold In_t_list;intros;b_auto.
Qed.


Lemma In_t_list_0_1:forall (e:t_list) (T:typ),
  In_t_list (t_cons e T) t_O (tshift t_O T).
Proof.
unfold In_t_list;simpl;intros;b_auto.
case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
Qed.

Lemma In_t_list_0_2:forall (e:t_list) (T S:typ),
  In_t_list (t_cons e T) t_O S -> S= tshift t_O T.
Proof.
unfold In_t_list;simpl.
intros e T S;case (t_nat_eq_dec t_O t_O);intros;b_auto.
rewrite <-(typ_eq_eq H1);auto.
intros;absurd (t_O = t_O);auto.
Qed.

Lemma In_t_list_S_1:forall  (e:t_list)(T T1:typ)(X:t_nat),
  X <> t_O ->
  In_t_list e (t_pred X) T -> In_t_list (t_cons e T1) X (tshift t_O T).
Proof.
unfold In_t_list;simpl;intros e T T1 X;case (t_nat_eq_dec X t_O);intros;b_auto.
rewrite <-(typ_eq_eq H2);auto.
Qed.

Lemma In_t_list_S_2:forall  (e:t_list)(T1 T:typ)(X:t_nat),
  X <> t_O ->
  In_t_list (t_cons e T1)  X T -> T = tshift t_O (get_t_list e (t_pred X)).
Proof.
unfold In_t_list;simpl;intros e T1 T X;case (t_nat_eq_dec X t_O);intros;b_auto.
rewrite <-(typ_eq_eq H2);auto.
Qed.

Lemma In_t_list_S_3:forall  (e:t_list)(T1 T2 T:typ)(X:t_nat),
  X <> t_O ->
  In_t_list (t_cons e T1) X T -> In_t_list (t_cons e T2) X T.
Proof.
unfold In_t_list;simpl;intros e T1 T2 T X;case (t_nat_eq_dec X t_O);intros;b_auto.
Qed.

Lemma In_t_list_eq:
  forall (e:t_list) (x:t_nat)(T1 T2:typ),
  In_t_list e x  T1 -> In_t_list e x T2 -> T1 = T2.
Proof.
unfold In_t_list;simpl;intros;b_auto.
rewrite <-(typ_eq_eq H2);auto.
rewrite <-(typ_eq_eq H3);auto.
Qed.

Lemma get_t_list_0:forall  (e:t_list)(T:typ),
  tshift t_O T = get_t_list (t_cons e T) t_O.
Proof.
induction e;simpl;intros;b_auto.
case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
Qed.

Lemma shift_get_t_list:forall  (e:t_list)(T:typ)(X:t_nat),
  X <> t_O ->
  get_t_list (t_cons e T)  X  = tshift t_O (get_t_list e (t_pred X)).
Proof.
induction e;simpl;intros T X;case (t_nat_eq_dec X t_O);intros;b_auto.
Qed.

(* t_length of the first argument is less or equal to that of the second *)

Fixpoint t_lengthes (e1 e2:t_list) {struct e1}:bool:=
  match e1, e2 with
  | t_nil        , _              => true
  | t_cons e1' T , t_nil          => false
  | t_cons e1' T1 , t_cons e2' T2 => t_lengthes e1' e2' 
  end.

Lemma t_lengthes_refl:forall (e:t_list),
  t_lengthes  e e.
Proof.
induction e;simpl;intros;b_auto.
Qed.

Hint Resolve t_lengthes_refl:core.


Lemma wf_t_ind_leng:forall (e e':t_list),
  t_lengthes  e e' -> 
  forall (X:t_nat), wf_t_ind e X -> wf_t_ind e' X.
Proof.
induction e;induction e';simpl;intros;b_auto.
case (t_nat_eq_dec X t_O);intros;b_auto.
apply IHe;auto.
apply wf_t_ind_prop2 with t;auto.
Qed.

Lemma wf_typ_leng:forall (T:typ) (e e':t_list),
  t_lengthes  e e' -> wf_typ e T -> wf_typ e' T.
Proof.
induction T; simpl in *; intros;b_auto.
apply wf_t_ind_leng with e;auto.
apply IHT2 with (t_cons e T1) ;simpl;auto.
Qed.

(* all elements of the first argument are within the second *)

Fixpoint t_list_le (e1 e2:t_list) {struct e1}:bool:=
  match e1, e2 with
  | t_nil        , _              => true
  | t_cons e1' T , t_nil          => false
  | t_cons e1' T1 , t_cons e2' T2 => t_list_le e1' e2' && typ_eq T1 T2
  end.

Lemma t_list_le_leng:forall (e e':t_list),
  t_list_le e e' -> t_lengthes e e'. 
Proof.
induction e;induction e';simpl;intros;b_auto.
Qed.

Lemma t_list_le_refl:forall (e:t_list),
   t_list_le  e e.
Proof.
induction e;simpl;intros;b_auto.
Qed.

Hint Resolve t_list_le_refl:core.

Lemma t_list_le_prop:forall (e:t_list)(X:t_nat)(T:typ),
  In_t_list e X T ->
  forall (e':t_list),t_list_le e e' -> In_t_list e' X T.
Proof.
induction e;induction e';simpl;intros;b_auto.
apply Contradiction;auto.
rewrite <-(typ_eq_eq H2).
case (t_nat_eq_dec X t_O);intros HX.
rewrite HX;rewrite HX in H;rewrite (In_t_list_0_2 H);auto.
apply In_t_list_0_1;auto.
rewrite In_t_list_S_2 with e t T X;auto.
apply In_t_list_S_1;auto.
apply IHe;auto.
apply get_In_t_list.
apply wf_t_ind_prop2 with t;auto.
apply In_t_list_wf with T;auto.
Qed.


Lemma wf_typ_t_cons:forall (T U V:typ) (e:t_list),
   wf_typ (t_cons e U) T -> wf_typ (t_cons e V) T.
Proof.
intros T;induction T;simpl;intros;b_auto.
apply wf_typ_leng with (t_cons (t_cons e U) T1);simpl;eauto.
Qed.


(******************************************************************************************)
(*      Subtyping  lemmas                                                                 *) (******************************************************************************************)

Lemma sub_wf0:forall (T U:typ)(e:t_list),
   sub e T U -> wf_t_list e.
Proof.
intros e T U H; induction H;simpl in *;intros;b_auto.
Qed.

Lemma sub_wf12:forall (T U:typ)(e:t_list),
   sub e T U -> wf_typ e T && wf_typ e U.
Proof.
intros T U e H; induction H;simpl in *;intros;b_auto.
apply In_t_list_wf with U;auto.
apply wf_typ_t_cons with T1;auto.
Qed.

Lemma sub_wf1:forall  (T U:typ)(e:t_list),
  sub e T U -> wf_typ e T.
Proof.
intros T U e H.
cut (TRUE (wf_typ e T && wf_typ e U)).
intros;b_auto.
apply sub_wf12 ;auto.
Qed.

Lemma sub_wf2:forall (T U:typ)(e:t_list),
  sub e T U -> wf_typ e U.
Proof.
intros T U e H.
cut (TRUE (wf_typ e T && wf_typ e U)).
intros;b_auto.
apply sub_wf12;auto.
Qed.

(* Lemma A.1 *)
Lemma sub_reflexivity:forall (T1 T2:typ)(e:t_list),
   wf_t_list e -> typ_eq T1 T2 -> wf_typ e T2 -> sub e T1 T2.
Proof.
intros T1; induction T1;intros T2 e H H1;rewrite <-(typ_eq_eq H1);intros.
apply SA_Refl_TVar;auto.
apply SA_Top; auto.
apply SA_Arrow;simpl in *;b_auto. 
apply SA_All;simpl in *;b_auto. 
apply IHT1_2;simpl in *;b_auto. 
Qed.

(* Lemma A.2 (1) *)

Lemma sub_extensionality:forall (e:t_list) (U V:typ),
  sub e U V ->
  forall (e':t_list),
  t_list_le  e e' -> wf_t_list e' -> sub e' U V.
Proof.
intros e U V H;induction H; intros.
apply SA_Top; auto; apply wf_typ_leng with (e:=e);auto.
apply t_list_le_leng;auto.
apply sub_reflexivity;auto.
simpl;apply wf_t_ind_leng with e;auto.
apply t_list_le_leng;auto.
apply SA_Trans_TVar with U;auto.
apply t_list_le_prop with e;auto.
apply SA_Arrow; auto.
apply SA_All; auto.
apply IHsub2;simpl;b_auto.
apply wf_typ_leng with e;auto.
apply t_list_le_leng;auto.
apply sub_wf1 with S1;auto. 
Qed.

(******************************************************************************************)
(*  narrow1 is narrowing of narrow 2                                                      *)
(******************************************************************************************)
Fixpoint narrow1  (e0:t_list)(M N:typ) (e:t_list){struct e}:t_list:=
  match e with
  | t_nil         => t_cons e0 M
  | t_cons e' T'  => t_cons (narrow1 e0 M N e' ) T'
  end.

Fixpoint narrow2 (e0:t_list) (M N:typ) (e:t_list){struct e}:t_list:=
  match e with
  | t_nil         => t_cons e0 N
  | t_cons e' T'  => t_cons (narrow2 e0 M N e' ) T'
  end.

Fixpoint wf_narrow (e0:t_list) (M N:typ) (e:t_list){struct e}:bool:=
  match e with
  | t_nil         => true 
  | t_cons e' T'  => wf_typ  (narrow2 e0 M N e' )  T' && wf_narrow e0 M N e'
  end.

Lemma narrow_leng:forall (e e0:t_list)(M N:typ),
  t_lengthes (narrow1 e0 M N e)  (narrow2 e0 M N e).
Proof.
intros e e0 M N; induction e;simpl;intros;b_auto.
Qed.

Lemma narrow_wf_t_list:forall (e e0:t_list)(M N:typ),
  sub e0 N M -> wf_narrow e0 M N e -> 
  wf_t_list (narrow1 e0 M N e) -> wf_t_list (narrow2 e0 M N e) .
Proof.
intros e e0 M N H0 H; induction e;simpl in *;intros;b_auto.
apply sub_wf1 with M;auto.
Qed.

Lemma In_t_list_narrow_ne:forall (e e0:t_list)(M N:typ)(X:t_nat)(T:typ), 
  X <> t_length e -> 
  In_t_list  (narrow1 e0 M N e)  X T -> In_t_list  (narrow2 e0 M N e)  X T.
Proof.
intros e; induction e;simpl;intros e0 M N X T H;auto.
rewrite  <- (t_S_pred H).
intros H3;apply In_t_list_S_3 with M;auto.
rewrite  (t_S_pred H);auto.
case (t_nat_eq_dec X  t_O);intros HX.
rewrite HX;intros H3;rewrite (In_t_list_0_2 H3);auto.
apply In_t_list_0_1;auto.
intros;rewrite In_t_list_S_2 with  (narrow1 e0 M N e) t T X;auto.
apply In_t_list_S_1;auto.
apply IHe; auto.
red;intros;cut (X = t_S (t_length e));auto.
rewrite <-H1;auto.
rewrite (t_S_pred HX);auto.
apply get_In_t_list.
apply wf_t_ind_prop2 with T;auto.
apply In_t_list_wf with T;auto.
apply In_t_list_S_3 with t;auto.
Qed.


(******************************************************************************************)
(*  insert2 is obtained by inserting elements in insert1                                  *)
(******************************************************************************************)

Fixpoint insert1 (e0:t_list) (T:typ) (e:t_list){struct e}:t_list:=
  match e with
  | t_nil          => e0
  | t_cons e' T'   => t_cons (insert1 e0 T e') T'
  end.

Fixpoint insert2 (e0:t_list) (T:typ) (e:t_list){struct e}:t_list:=
  match e with
  | t_nil          => t_cons e0 T
  | t_cons e' T'   => t_cons (insert2 e0 T e') (tshift (t_length e') T')
  end.

Lemma  In_t_list_insert_0:
  forall (X:t_nat) (e0:t_list) (T0 T:typ),
  In_t_list e0 X T -> In_t_list (t_cons e0 T0) (t_semi_S t_O X) (tshift t_O T).
intros X e0 T0 T H.
rewrite t_semi_S_0_n;apply In_t_list_S_1;auto.
apply t_O_S;auto.
rewrite  t_pred_Sn;auto.
Qed.
 
Lemma In_t_list_insert:
  forall (e:t_list) (X:t_nat)(e0:t_list)(T0 T:typ),
  In_t_list (insert1 e0 T0 e) X T ->
  In_t_list  (insert2 e0 T0 e) (t_semi_S (t_length e) X) (tshift (t_length e) T).
Proof.
intros  e; induction e;simpl.
apply In_t_list_insert_0;auto.
intros X;case (t_nat_eq_dec X t_O);intros HX.
rewrite HX;intros;rewrite t_semi_S_S_0.
rewrite (In_t_list_0_2 H);auto.
rewrite  <- tshift_tshift_prop;auto.
apply In_t_list_0_1;auto.
intros;rewrite In_t_list_S_2 with (insert1 e0 T0 e) t T X;auto.
rewrite  <-tshift_tshift_prop.
apply In_t_list_S_1;auto.
apply t_semi_S_3;auto.
rewrite (t_semi_S_1 (t_length e) HX);
apply IHe;auto.
apply get_In_t_list;auto.
apply wf_t_ind_prop2 with t;auto.
apply In_t_list_wf with T;auto.
Qed.

Lemma wf_t_ind_insert_0:
  forall (X:t_nat) (e0:t_list) (T0:typ),
  wf_t_ind e0 X -> wf_t_ind (t_cons e0 T0) (t_semi_S t_O X).
intros X e0 T0 H;rewrite t_semi_S_0_n;apply wf_t_ind_prop1;auto.
apply t_O_S;auto.
rewrite  t_pred_Sn;auto.
Qed.

Lemma wf_t_ind_insert:
  forall (e:t_list) (X:t_nat)(e0:t_list)(T0 :typ),
  wf_t_ind (insert1 e0 T0 e) X ->
  wf_t_ind (insert2 e0 T0 e) (t_semi_S (t_length e) X).
Proof.
intros  e; induction e;simpl.
apply wf_t_ind_insert_0;auto.
intros X;case (t_nat_eq_dec  X  t_O);intros HX.
rewrite HX;auto.
rewrite t_semi_S_S_0;auto.
case (t_nat_eq_dec  t_O  t_O);auto.
intros;absurd (t_O = t_O);auto.
case (t_nat_eq_dec (t_semi_S (t_S (t_length e)) X) t_O);intros;b_auto.
rewrite (t_semi_S_1 (t_length e) HX).
apply IHe;auto.
Qed.

Lemma insert_wf_typ:forall (T T0:typ)(e e0:t_list) , 
  wf_typ (insert1 e0 T0 e) T ->
  wf_typ (insert2 e0 T0 e) (tshift (t_length e) T). 
Proof.
intros T;induction T;simpl;intros;b_auto.
apply wf_t_ind_insert;auto.
replace (t_S (t_length e)) with (t_length (t_cons e T1));auto.
apply IHT2 with (e:=t_cons e T1)(e0:=e0)(T0:=T0);auto.
Qed.

Lemma wf_typ_weakening:forall (e:t_list) (T U:typ),
  wf_typ e T -> wf_typ e U -> wf_typ (t_cons e U) (tshift t_O T).
Proof.
intros e T;intros.
apply insert_wf_typ with (e0:=e)(e:=t_nil)(T0:=U);auto.
Qed.

Lemma insert_wf:forall (e:t_list) (T:typ)(e0:t_list), 
  wf_typ e0 T -> wf_t_list (insert1 e0 T e)->wf_t_list (insert2 e0 T e). 
Proof.
intros e;induction e; simpl;intros;b_auto.
apply insert_wf_typ;auto.
Qed.

Lemma sub_weakening_ind:
  forall (e:t_list)(U V:typ),
  sub e U V ->
  forall (e0 e1:t_list)(T0:typ) , 
  wf_typ e0 T0 -> e = insert1 e0 T0 e1 ->
  sub (insert2 e0 T0 e1) (tshift (t_length e1) U) (tshift (t_length e1)  V). 
Proof.
intros e U V H;induction H; intros;auto.
apply SA_Top.
apply insert_wf;auto.
rewrite <- H2;auto.
apply insert_wf_typ.
rewrite <- H2;auto.
simpl;apply SA_Refl_TVar.
apply insert_wf;auto.
rewrite <- H2;auto.
apply  wf_t_ind_insert;auto.
rewrite <- H2;auto.
simpl;apply SA_Trans_TVar with (tshift (t_length e1) U);auto.
apply In_t_list_insert;auto.        
rewrite <- H2;auto.
simpl;apply SA_Arrow; auto.
simpl;apply SA_All; auto.
replace (t_S (t_length e1)) with (t_length (t_cons e1 T1));auto.
apply  IHsub2 with (e1:=t_cons e1 T1)(e0:=e0)(T0:=T0);auto.
rewrite H2;auto.
Qed.

(* Lemma A.2 (2) *)
 
Lemma sub_weakening:forall (e:t_list) (T U V:typ),
  wf_typ e V -> sub e T U -> sub (t_cons e V) (tshift t_O T) (tshift t_O U).
Proof.
intros e T U V H0 H.
apply sub_weakening_ind with (e:=e)(e0:=e)(e1:=t_nil)(T0:=V);auto.
Qed.


(******************************************************************************************)
(*  Transitivity and Narrowing  (Lemma A.3)                                               *)
(*  By induction on structural depth of a type                                            *)
(******************************************************************************************)

Lemma narrow_sub:forall (e e0:t_list)(M N U V:typ),
   sub e0 N M -> wf_narrow e0 M N e ->
   In_t_list (narrow1 e0 M N e) (t_length e) U -> 
   In_t_list (narrow2 e0 M N e) (t_length e) V -> sub (narrow2 e0 M N e) V U.
Proof.
intros e;induction e;auto;simpl;intros.
rewrite  (In_t_list_0_2 H1).
rewrite  (In_t_list_0_2 H2).
replace t_O with (t_length t_nil);simpl;auto.
apply sub_weakening_ind with (e:=e0)(e0:=e0)(e1:=t_nil)(T0:=N);auto.
apply (sub_wf1 H).
rewrite  In_t_list_S_2 with (narrow1 e0 M N e) t U (t_S (t_length e));auto.
rewrite  In_t_list_S_2 with (narrow2 e0 M N e) t V (t_S (t_length e));auto.
apply sub_weakening;b_auto.
apply IHe;b_auto.
rewrite t_pred_Sn;auto.
apply get_In_t_list;auto.
apply wf_t_ind_prop3 with t;auto.
apply In_t_list_wf with U;auto.
rewrite t_pred_Sn;auto.
apply get_In_t_list;auto.
apply wf_t_ind_prop3 with t;auto.
apply In_t_list_wf with V;auto.
apply t_O_S;auto.
apply t_O_S;auto.
Qed.

Lemma sub_t_var:forall (e e0:t_list)(M N U:typ),
  sub e0 N M -> wf_narrow e0 M N e -> In_t_list (narrow1 e0 M N e) (t_length e) U -> 
  sub  (narrow2 e0 M N e) (t_var (t_length e)) U.
Proof.
intros e;induction e;auto;intros.
apply SA_Trans_TVar with (get_t_list (t_cons e0 N) t_O).
apply get_In_t_list;auto.
simpl;case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
apply narrow_sub;auto.
apply get_In_t_list;auto.
simpl;case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
apply SA_Trans_TVar with
(get_t_list (narrow2 e0 M N (t_cons e t) ) (t_length (t_cons e t))).
apply get_In_t_list;auto.
apply wf_t_ind_leng with (t_cons (narrow1 e0 M N e) t);auto.
simpl;apply narrow_leng;auto.
apply In_t_list_wf with U;auto.
apply narrow_sub;auto.
apply get_In_t_list;auto.
apply wf_t_ind_leng with (t_cons (narrow1 e0 M N e) t);auto.
simpl;apply narrow_leng;auto.
apply In_t_list_wf with U;auto.
Qed.

Lemma sub_narrowing0:forall (T1 T2:typ)(e0:t_list),
  sub e0 T2 T1 ->
  (forall  (M N:typ)(e1:t_list), 
  sub (narrow2 e0 T1 T2 e1)  M (get_t_list (narrow1 e0 T1 T2 e1) (t_length e1)) -> 
  sub (narrow2 e0 T1 T2 e1)  (get_t_list (narrow1 e0 T1 T2 e1) (t_length e1)) N ->
  sub (narrow2 e0 T1 T2 e1)  M N) ->
  forall (e:t_list)(M N:typ), sub e M N->
  forall (e1:t_list), wf_narrow e0 T1 T2 e1 ->
  e = narrow1 e0 T1 T2 e1 -> sub (narrow2 e0 T1 T2 e1) M N.
Proof.
intros  T1 T2 e0 H0 H  e M N H1.
induction H1;intros;auto.
apply SA_Top;auto.
apply narrow_wf_t_list ;auto.
rewrite<- H4;auto.
apply wf_typ_leng with e;auto.
rewrite H4;auto.
apply narrow_leng;auto.
apply SA_Refl_TVar;simpl;auto.
apply narrow_wf_t_list;auto.
rewrite <-H4;auto.
apply wf_t_ind_leng with e;auto.
rewrite H4;auto.
apply narrow_leng;auto.
case (t_nat_eq_dec X (t_length e1)).
intro E0.
apply H.
rewrite E0;apply sub_t_var;auto.
rewrite <-H4;auto.
apply get_In_t_list.
rewrite <-E0.
apply In_t_list_wf with U;auto.
rewrite <-H4;auto.
rewrite <-In_t_list_eq with e  (t_length e1) U (get_t_list e (t_length e1));eauto.
rewrite <-E0;auto.
apply get_In_t_list.
rewrite <-E0.
apply In_t_list_wf with U;auto.
intros;apply SA_Trans_TVar with U; eauto.
apply In_t_list_narrow_ne;auto.
rewrite <-H4;auto.
apply SA_Arrow; eauto.
apply SA_All; eauto.
apply IHsub2 with (e1:=t_cons e1 T0);simpl;b_auto.
apply wf_typ_leng with e;auto.
rewrite H2;auto.
apply narrow_leng;auto.
apply sub_wf1 with S1;auto.
simpl;rewrite H2;auto.
Qed.

Fixpoint max (n m:nat) {struct n}:nat:=
  match n, m with
  | O, _ => m
  | S n', O => n
  | S n', S m' => S (max n' m')
  end.

Lemma le_max_l:forall n m, n <= max n m.
Proof.
induction n; intros; simpl in |- *; auto with arith.
elim m; intros; simpl in |- *; auto with arith.
Qed.

Lemma le_max_r:forall n m, m <= max n m.
Proof.
induction n; simpl in |- *; auto with arith.
induction m; simpl in |- *; auto with arith.
Qed.

Fixpoint depth (T:typ):nat:=
  match T with
  | t_var _          => O
  | top              => O
  | arrow T1 T2 => S (max (depth T1) (depth T2))
  | all T1 T2      => S (max (depth T1) (depth T2))
  end.

Lemma shift_preserves_depth:forall (T:typ)(n:t_nat),
   depth (tshift n T) = depth T.
Proof.
induction T;auto; simpl;intros n; rewrite IHT1; rewrite IHT2; auto.
Qed.

Lemma depth_get_t_list:forall (e e0:t_list) (T1 T2:typ),
  depth (get_t_list (narrow1 e0 T1 T2 e) (t_length e)) = depth T1.
Proof.
induction e;simpl;intros;auto;rewrite shift_preserves_depth;auto.
case (t_nat_eq_dec t_O t_O);auto.
intros;absurd (t_O = t_O);auto.
case (t_nat_eq_dec (t_S (t_length e)) t_O);auto.
intros;absurd (t_S (t_length e) = t_O);auto.
apply t_O_S;auto.
rewrite t_pred_Sn;auto.
Qed.

Lemma sub_transitivity0:forall  U Q:typ,
  (forall (M N:typ) (e e1:t_list),
  sub (narrow2 e Q U e1) M (get_t_list (narrow1 e Q U e1) (t_length e1)) ->
  sub (narrow2 e Q U e1) (get_t_list (narrow1 e Q U e1) (t_length e1)) N ->
  sub (narrow2 e Q U e1) M N) ->
  forall (e:t_list) (M N:typ),
  sub e U Q -> sub (t_cons e Q) M N -> sub (t_cons e U) M N. 
Proof.
intros U Q H e M N;intros.
apply sub_narrowing0  with (T1:=Q)(T2:=U)(e:= (t_cons e Q))(e0:=e)(e1:=t_nil);auto.
Qed.

Lemma sub_transitivity:forall (e:t_list) (U Q T:typ),
   sub e U Q -> sub e Q T -> sub e U T .
Proof.
cut (forall (n:nat) (Q:typ), lt (depth Q)  n -> 
forall (e:t_list) (U T:typ), sub e U Q -> sub e Q T -> sub e U T).
intros H e U Q T ; apply (H (S (depth Q)));auto with arith.
induction n.
intros; absurd (depth Q <0);auto with arith.
intros H e U Q T H1 H2.
induction H1;simpl in *;intros;b_auto.
inversion_clear H2;auto.
apply SA_Top; auto.
apply SA_Trans_TVar with U;auto.
inversion_clear H2;simpl in *;intros;b_auto.
apply SA_Top; simpl; intros;b_auto.
apply sub_wf2 with T1;auto.
apply sub_wf1 with T2;simpl;intros;b_auto.
apply SA_Arrow.
apply IHn with T1;auto.
apply le_lt_trans with (max (depth T1) (depth T2));auto with arith.
apply le_max_l.
apply IHn with T2;auto.
apply le_lt_trans with (max (depth T1) (depth T2));auto with arith.
apply le_max_r.
inversion_clear H2;simpl in *;intros;b_auto.
apply SA_Top; simpl; intros;b_auto.
apply sub_wf2 with T1;auto.
apply wf_typ_t_cons with (U:= T1);simpl; intros;b_auto.
apply sub_wf1 with T2;simpl;intros;b_auto.
apply SA_All.
apply IHn with T1;auto.
apply le_lt_trans with (max (depth T1) (depth T2));auto with arith.
apply le_max_l.
intros;apply IHn with T2;auto.
apply le_lt_trans with (max (depth T1) (depth T2));auto with arith.
apply le_max_r.
apply sub_transitivity0 with T1;auto.
intros;apply IHn with (get_t_list (narrow1 e1 T1 T0 e2) (t_length e2)) ;auto.
rewrite depth_get_t_list.
apply le_lt_trans with (max (depth T1) (depth T2));auto with arith.
apply le_max_l.
Qed.

Lemma sub_narrowing:forall (e1 e0:t_list)(P Q M N:typ),
  wf_narrow e0 Q P e1 -> sub e0 P Q ->
  sub (narrow1 e0 Q P e1) M N -> sub (narrow2 e0 Q P e1) M N.
Proof.
intros e1 e0 P Q;intros.
apply sub_narrowing0 with (narrow1 e0 Q P e1);auto.
intros U T e;apply  sub_transitivity.
Qed.

