(*****************************************)
(*   Submission for PoplMark challenges  *)
(*   Jevgenijs Sallinens, August 2005    *) 
(*      Evaluation relation (red.v)      *) 
(*****************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Bool.
Require Import tactics.
Require Import sub_defs.
Require Import sub.
Require Import typ_defs.
Require Import typ.
Require Import red_defs.
Import M_T_Nat.

(******************************************************************************************)
(*      General lemmas                                                                    *) (******************************************************************************************)

Lemma fun_value0:forall (t:term) (T:typ),
  value t->typing empty t T ->
  forall (T1 T2:typ),
  T =arrow T1 T2 ->  t = abs (first t) (second t).
Proof.
set (e:=empty).
cut (e = empty);auto.
intros H1 t T H0 H.
induction H;simpl in *;intros;subst e;b_auto.
discriminate.
rewrite H3 in H2; inversion H2.
apply Contradiction;auto.
eauto.
Qed.

Lemma fun_value:forall (t:term) (T1 T2:typ),
  value t -> typing empty t (arrow T1 T2)->
  t = abs (first t) (second t).
Proof.
intros t T1 T2;intros.
apply fun_value0 with (arrow T1 T2) T1 T2;auto.
Qed.

Lemma typefun_value0:forall (t:term) (T:typ),
  value t -> typing empty t T ->
  forall (T1 T2:typ),
  T =all T1 T2 ->  t = tabs (t_first t) (t_second t).
Proof.
set (e:=empty).
cut (e = empty);auto.
intros H1 t T H0 H.
induction H;simpl in *;intros;subst e;b_auto.
discriminate.
rewrite H3 in H2; inversion H2.
apply Contradiction;auto.
eauto.
Qed.

Lemma typefun_value:forall (t:term) (T1 T2:typ),
  value t -> typing empty t (all T1 T2) ->
  t = tabs (t_first t) (t_second t).
Proof.
intros t T1 T2;intros.
apply typefun_value0 with (all T1 T2) T1 T2;auto.
Qed.

(* Explicit analogue for E-AppAbs rule *)
  
Lemma appabs:forall (t11:typ) (t12 t2:term),
  value t2 -> red (app (abs t11 t12) t2) (subst t12 t_O t2).
Proof.
intros t11 t12 t2 H.
set (t:= subst t12 t_O t2).
cut (t = subst t12 t_O t2).
generalize t;clear t;intros t H1.
induction t2;simpl in *;and_intros.
induction t;simpl in *;and_intros;rewrite <-H1;simpl in *;and_intros.
rewrite <- beq_t_nat_refl;auto.
induction t;simpl in *;and_intros;rewrite <-H1;simpl in *;and_intros.
rewrite <- beq_t_nat_refl;auto.
auto.
Qed.  

(* Explicit analogue for E-TAppTAbs rule *)

Lemma tapptabs:forall (t11 t2:typ) (t12:term),
  red (tapp (tabs t11 t12) t2) (subst_typ t12 t_O t2).
Proof.
intros t11 t2 t12.
set (t:=subst_typ t12 t_O t2).
cut (t =subst_typ t12 t_O t2).
generalize t;clear t;intros t H.
induction t2;simpl in *;b_auto.
induction t;simpl in *;and_intros;rewrite <-H;simpl in *;and_intros.
rewrite <- beq_t_nat_refl;auto.
induction t;simpl in *;and_intros;rewrite <-H;simpl in *;and_intros.
rewrite <- beq_t_nat_refl;auto.
induction t;simpl in *;and_intros;rewrite <-H;simpl in *;and_intros.
rewrite <- beq_t_nat_refl;auto.
induction t;simpl in *;and_intros;rewrite <-H;simpl in *;and_intros.
rewrite <- beq_t_nat_refl;auto.
auto.
Qed.

Lemma appfun:forall t1 t1' t2:term,
  red t1 t1' -> red (app t1 t2) (app t1' t2).
Proof.
intros;simpl in *;and_intros.
apply term_refl1 with t2;auto.
apply term_refl1 with t2;auto.
Qed.

Lemma apparg:forall t1 t2 t2':term,
  value t1 -> red t2 t2' -> red (app t1 t2) (app t1 t2').
Proof.
intros;simpl in *;and_intros.
apply term_refl1 with t1;auto.
apply term_refl1 with t1;auto.
Qed.

(******************************************************************************************)
(*      Progress lemma (Lemma A.16)                                                       *) (******************************************************************************************)

Theorem progress:
  forall (t:term) (U:typ),
  typing empty t U -> (value t -> false) -> red t (progr t).
Proof.
set (e:=empty).
cut (e = empty);auto.
intros H0 t U H;induction H;unfold progr; fold progr;intros;subst e;b_auto.
apply Decide with (value t1);intros HA.
rewrite (TrueEq HA);auto.
apply Decide with (value t2);intros HB.
rewrite (TrueEq HB);auto.
rewrite (fun_value  HA H).
replace (value (abs (first t1) (second t1))) with true;auto.
apply appabs;auto.
rewrite (FalseEq HB);auto.
apply apparg;auto.
rewrite (FalseEq HA);auto.
apply appfun;auto.
apply Decide with (value t1);intros HA.
rewrite (TrueEq HA);auto.
rewrite (typefun_value  HA H).
replace (value (abs (first t1) (second t1))) with true;auto.
apply tapptabs;auto.
rewrite (FalseEq HA);auto.
inversion H1;simpl in *;b_auto;intros;apply typ_refl1 with T2;b_auto.
Qed.
 
(******************************************************************************************)
(*  Narrowing for the typing rule (Lemma A.7)                                             *) (******************************************************************************************)
Lemma typing_narrowing_ind:
 forall (e:env) (t:term) (U:typ), 
 typing e t U ->
 forall (e1 e0:env)(M N:typ),  
 e = v_narrow1 e0 M N e1 -> sub (env_types e0) N M -> wf_v_narrow e0 M N e1->
 typing (v_narrow2 e0 M N e1) t U.
Proof.
intros e t U H2;induction H2;intros.
apply T_Var;auto.
apply v_narrow_wf_env; auto.
rewrite <- H1;auto.
apply In_env_var_narrow;auto.
rewrite <- H1;auto.
apply T_Abs.
apply IHtyping with (e1:=(evar e1 T1))(e0:= e0)(M:= M)( N:=N);auto.
simpl;rewrite  H;auto.
simpl;b_auto.
apply wf_typ_leng with (env_types (v_narrow1 e0 M N e1));auto.
apply v_narrow_leng;auto.
apply wf_env_vars1;auto.
rewrite <- H;auto.
apply typing_wf1 with t T2;auto.
eapply T_App; eauto.
apply T_Tabs.
apply IHtyping with (e1:=(ebound e1 T1))(e0:= e0)(M:= M)( N:=N);auto.
simpl;rewrite  H;auto.
simpl;b_auto.
apply wf_typ_leng with (env_types (v_narrow1 e0 M N  e1));auto.
apply v_narrow_leng;auto.
apply wf_env_bounds1;auto.
rewrite <- H;auto.
apply typing_wf1 with t T2;auto.
eapply T_Tapp; eauto.
rewrite narrow_2;auto.
apply  sub_narrowing;auto.
apply wf_narrows;auto.
rewrite <- narrow_1;auto.
rewrite <- H0;auto.
apply T_Sub with T1;eauto.
rewrite narrow_2;auto.
apply sub_narrowing;auto.
apply wf_narrows;auto.
rewrite <- narrow_1;auto.
rewrite <- H0;auto.
Qed.

(******************************************************************************************)
(*      Inversions of typing rules                                                        *) (******************************************************************************************)

Lemma T_Abs_inversion:forall (e:env)(T0:typ)(t':term), 
  typing e t' T0 ->
  forall (t t_0 t2:term) (T1 T2 T3:typ), 
  t' = abs T1 t -> sub (env_types e) T0 (arrow T2 T3) ->
  typing e t2 T2 ->
  typing e (subst t t_O t2) T3.
Proof.
intros e T0 t' H;induction H;intros; try discriminate.
inversion_clear H1;auto.
apply T_Sub with T2;auto.
apply subst_preserves_typing with T1;auto.
injection H0; intros E2 E3.
rewrite <- E2;auto.
apply T_Sub with T3;auto.
apply IHtyping with T0 T3;auto.
apply sub_transitivity with T2;auto.
Qed.

Lemma T_Tabs_inversion:forall (e:env)(T0:typ)(t':term),
  typing e t' T0 ->
  forall (t:term) (T1 T2 T3:typ),
  t' = tabs T1 t -> sub (env_types e) T0 (all T2 T3) ->
  typing (ebound e T2) t T3.
intros e T0 t' H;induction H;intros; try discriminate.
inversion_clear H1;auto.
apply T_Sub with T2;auto.
apply typing_narrowing_ind with  (e:=(ebound e T1))(e1:=empty)(e0:=e)(M:=T1)(N:=T3);auto.
injection H0; intros E2 E3; rewrite <- E2;auto.
apply IHtyping with T0;auto.
apply sub_transitivity with T2;auto.
Qed.

(******************************************************************************************)
(*      Preservation  (Lemma A.20)                                                        *) (******************************************************************************************)

Theorem preservation:
  forall (e:env) (t:term)(U:typ),
  typing e t U -> forall  (t':term), red t t' -> typing e t' U.
Proof.
intros e t U H1;induction H1;intros.
apply Contradiction;induction t';intros;b_auto.
apply Contradiction;induction t';intros;b_auto.
apply Decide with (is_subst t2 t' t1);intros H1.
induction t1;simpl in *;intros;b_auto.
rewrite (term_eq_eq H1).
intros;apply T_Abs_inversion with  (arrow T11 T12) (abs t t1) t T11;auto.
apply sub_reflexivity;auto.
apply wf_env_list;auto.
apply (typing_wf1 H1_);auto.
apply (typing_wf2 H1_);auto.
induction t';simpl in *;intros;b_auto.
apply T_App with T11;and_intros2.
rewrite <-(term_eq_eq H3);auto.
rewrite <-(term_eq_eq H0);auto.
apply Contradiction;induction t';intros;b_auto.
apply Decide with (is_subst_typ T2 t' t1);intros.
induction t1;simpl in *;intros;b_auto.
rewrite (term_eq_eq H2).
apply subst_typ_preserves_typing with T11;auto.
apply T_Tabs_inversion with  (all T11 T12) (tabs t t1) t;auto.
apply sub_reflexivity;auto.
apply wf_env_list;auto.
apply (typing_wf1 H1);auto.
apply (typing_wf2 H1);auto.
induction t';simpl in *;intros;and_intros2.
rewrite <-(typ_eq_eq H3);auto.
apply T_Tapp with T11;auto.
apply T_Sub with T1; auto.
Qed.
(******************************************************************************************)

