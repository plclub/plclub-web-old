(*********************************************************)
(*   Submission for PoplMark challenges                  *)
(*   Jevgenijs Sallinens, August 2005                    *) 
(*   Definitions for typing relation (typ_defs.v)        *) 
(*********************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Bool.
Require Import tactics.
Require Import sub_defs.
Import M_T_Nat.

(* enviroments *)

Inductive env:Set:=
  | empty:env
  | evar :env -> typ -> env
  | ebound:env -> typ -> env.

Fixpoint env_types (e:env) {struct e}:t_list:=
  match e with
  | empty       => t_nil
  | evar e' _   => env_types e'
  | ebound e' T => t_cons (env_types e') T
  end.

Fixpoint b_length (e:env){struct e}:t_nat:=
  match e with
  | empty          => t_O
  | evar e' T'     => b_length e'
  | ebound e' T'   => t_S (b_length e')
  end.

Fixpoint v_length (e:env){struct e}:t_nat:=
  match e with
  | empty          => t_O
  | evar e' T'     => t_S (v_length e')
  | ebound e' T'   => v_length e'
  end.

(* well-founded enviroments *)
    
Fixpoint wf_env (e:env){struct e}:bool:=
  match e with
  | empty      => true
  | evar e T   => wf_typ (env_types e) T && wf_env e
  | ebound e T => wf_typ (env_types e) T && wf_env e
  end.

(* well-founded indices of enviroments *)

Fixpoint wf_v_ind (e:env) (x:t_nat) {struct e}:bool:=
  match e with
  | empty       => false
  | ebound e' _ => wf_v_ind e' x
  | evar e' T   => if (t_nat_eq_dec x t_O) then true else wf_v_ind e' (t_pred x)
  end.

(* get (shifted) type for given index *)

Fixpoint get_v_env (e:env) (x:t_nat) {struct e}:typ:=
  match e with
    empty       => top
  | ebound e' _ => tshift t_O (get_v_env e' x)
  | evar e' T   => if (t_nat_eq_dec x t_O) then T else get_v_env e' (t_pred x)
  end.

(* types within enviroments *)

Definition In_env_var (e:env) (X:t_nat)(T:typ):=wf_v_ind e X && typ_eq T (get_v_env e X).

(* terms *)
Inductive term:Set:=
  | var:t_nat-> term
  | abs:typ -> term -> term
  | app:term -> term -> term
  | tabs:typ -> term -> term
  | tapp:term -> typ -> term.

(* well-founded terms *)

Fixpoint wf_term (e:env) (t:term) {struct t}:bool:=
  match t with
  | var x        => wf_env e && wf_v_ind e x
  | abs T1 t2    => wf_typ (env_types e) T1  && wf_term (evar e T1) t2
  | app t1 t2    => wf_term e t1 && wf_term e t2
  | tabs T1 t2   => wf_typ (env_types e) T1  && wf_term (ebound e T1) t2
  | tapp t1 T2   => wf_term e t1 && wf_typ (env_types e) T2
  end.

(*  decidable equality on terms  *)
Fixpoint term_eq (t1 t2:term) {struct t1}:bool:=
  match t1, t2 with
  | var x      ,var x'     => beq_t_nat x x'
  | abs t1 t2  ,abs s1 s2  => typ_eq t1 s1 && term_eq t2 s2
  | app t1 t2  ,app s1 s2  => term_eq t1 s1 && term_eq t2 s2
  | tabs t1 t2 ,tabs s1 s2 => typ_eq t1 s1 && term_eq t2 s2
  | tapp t1 t2 ,tapp s1 s2 => term_eq t1 s1 && typ_eq t2 s2
  | _          , _         => false
  end.

(* Shifting of terms *)
Fixpoint shift (x:t_nat) (t:term) {struct t}:term:=
  match t with
  | var y      => var (t_semi_S x y)
  | abs T1 t2  => abs T1 (shift (t_S x) t2)
  | app t1 t2  => app (shift x t1) (shift x t2)
  | tabs T1 t2 => tabs T1 (shift x t2)
  | tapp t1 T2 => tapp (shift x t1) T2
  end.

Fixpoint shift_typ (X:t_nat) (t:term) {struct t}:term:=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tshift X T1) (shift_typ X t2)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | tabs T1 t2 => tabs (tshift X T1) (shift_typ (t_S X) t2)
  | tapp t1 T2 => tapp (shift_typ X t1) (tshift X T2)
  end.

(* Substituting of terms *)

Fixpoint subst (t:term) (x:t_nat) (t':term) {struct t}:term:=
  match t with
  | var y      => if (t_nat_eq_dec y x) then t' else var (t_semi_P y x)
  | abs T1 t2  => abs T1 (subst t2 (t_S x) (shift t_O t'))
  | app t1 t2  => app (subst t1 x t') (subst t2 x t')
  | tabs T1 t2 => tabs T1 (subst t2 x  (shift_typ t_O t'))
  | tapp t1 T2 => tapp (subst t1 x t') T2
  end.

Fixpoint subst_typ (t:term) (X:t_nat) (T:typ) {struct t}:term:=
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tsubst T1 X T) (subst_typ t2 X T)
  | app t1 t2  => app (subst_typ t1 X T) (subst_typ t2 X T)
  | tabs T1 t1 => tabs (tsubst T1 X T) (subst_typ t1 (t_S X) (tshift t_O T))
  | tapp t1 T2 => tapp (subst_typ t1 X T) (tsubst T2 X T)
  end.

(******************************************************************************************)
(*      Typing relation  (undecidable)                                                    *) (******************************************************************************************)

Inductive typing:env -> term -> typ -> Prop:=
  | T_Var:
      forall (e:env) (x:t_nat)(T:typ),
      wf_env e->In_env_var e x T -> typing e (var x) T
  | T_Abs:
     forall (e:env) (t:term) (T1 T2:typ),
      typing (evar e T1) t T2 ->
      typing e (abs T1 t) (arrow T1 T2)
  | T_App:
      forall (e:env) (t1 t2:term) (T11 T12:typ),
      typing e t1 (arrow T11 T12) ->
      typing e t2 T11 -> typing e (app t1 t2) T12
  | T_Tabs:
      forall (e:env) (t:term) (T1 T2:typ),
      typing (ebound e T1) t T2 -> typing e (tabs T1 t) (all T1 T2)
  | T_Tapp:
      forall (e:env) (t1:term) (T11 T12 T2:typ),
      typing e t1 (all T11 T12) ->
      sub (env_types e) T2 T11 -> typing e (tapp t1 T2) (tsubst T12 t_O T2)
  | T_Sub:
      forall (e:env) (t:term) (T1 T2:typ),
      typing e t T1 -> sub (env_types e) T1 T2 -> typing e t T2.
(******************************************************************************************)
