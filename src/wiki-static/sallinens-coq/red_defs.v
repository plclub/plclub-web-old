(*********************************************************)
(*   Submission for PoplMark challenges                  *)
(*   Jevgenijs Sallinens, August 2005                    *) 
(*   Definitions for evaluation relation (red_defs.v)    *) 
(*********************************************************)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Bool.
Require Import tactics.
Require Import sub_defs.
Require Import typ_defs.
Import M_T_Nat.

(* closed values (canonical forms) *)
Definition value (t:term):bool:=
  match t with
  | abs _ _  => true
  | tabs _ _ => true
  | _        => false
  end.

Definition first (T:term):typ:=
  match T with
  | abs t1 t2  => t1
  | _          => top
  end.

Definition second (T:term):term:=
  match T with
  | abs t1 t2  => t2
  | _          => T
  end.

Definition t_first(T:term):typ:=
  match T with
  | tabs t1 e1 => t1
  | _          => top
  end.

Definition t_second (T:term):term:=
  match T with
  | tabs t1 e1 => e1
  | _          => T
  end.

Definition is_subst (T1 T2 T:term):bool:=
  match T with
  | abs t1 t2  => term_eq T2 (subst t2 t_O T1)
  | _          => false
  end.
  
Definition is_subst_typ (T1:typ)(T2 T:term):bool:=
  match T with
  | tabs t1 e1 => term_eq T2 (subst_typ e1 t_O T1)
  | _          => false
  end.

(******************************************************************************************)
(*   Evaluation relation                                                                  *)
(******************************************************************************************)

Fixpoint red (T1 T2:term){struct T1}:bool:=
  match T1, T2 with
  | app t1 t2 ,  var x       => value t2 && is_subst t2 (var x) t1
  | app t1 t2 ,  abs e1 e2   => value t2 && is_subst t2 (abs e1 e2) t1
  | app t1 t2 ,  app e1 e2   => (value t1 && term_eq t1 e1 && red t2 e2) ||
                                (term_eq t2 e2 && red t1 e1) ||
                                (value t2 && is_subst t2 (app e1 e2) t1)
  | app t1 t2 ,  tabs e1 e2  => value t2 && is_subst t2 (tabs e1 e2) t1
  | app t1 t2 ,  tapp e1 e2  => value t2 && is_subst t2 (tapp e1 e2) t1
  | tapp t1 t2,  var x       => is_subst_typ t2 (var x) t1
  | tapp t1 t2,  abs e1 e2   => is_subst_typ t2 (abs e1 e2) t1
  | tapp t1 t2,  app e1 e2   => is_subst_typ t2 (app e1 e2) t1
  | tapp t1 t2,  tabs e1 e2  => is_subst_typ t2 (tabs e1 e2) t1
  | tapp t1 t2,  tapp e1 e2  => (typ_eq t2 e2 && red t1 e1) ||
                                is_subst_typ t2 (tapp e1 e2) t1
  | _         ,  _           => false
  end.

(******************************************************************************************)
(*   Progress operator (reduction step)                                                   *) 
(******************************************************************************************)

Fixpoint progr (t:term){struct t}:term:=
  match t with
      | var x        => var x 
      | abs  t1 t2   => abs t1 t2
      | app  t1 t2   => if (value t1) then 
          (if (value t2) then (subst (second t1) t_O t2) else (app t1 (progr t2)))
          else (app (progr t1) t2)
      | tabs t1 t2   => tabs t1 t2
      | tapp t1 t2   => if (value t1) then (subst_typ (t_second t1) t_O t2) else
          (tapp (progr t1) t2)                  
   end.

(******************************************************************************************)

