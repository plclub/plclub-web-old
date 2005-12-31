(* ============================================================================ 
                       Tactics for  POPLmark challenges 
                             Jevgenijs Sallinens 
                              June/November 2005
   ============================================================================ *)

(* ============================================================================ *)
(**
Some obvious results about booleans are given without proof as axioms, just to reduce space and
efforts.
Axioms and tactics connected with [negb] are not used in this development, but
provided for comletness and possible will be used in future additions.
*)
(* ============================================================================ *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import Bool.

(* ============================================================================ *)
(**  * Booleans *)
(* ============================================================================ *)

(**
Inductive bool : Set :=
  | true : bool
  | false : bool.

We shall make correspondence between booleans and propositions by
introducing function TRUE :bool -> Prop.
*)

Definition TRUE (x:bool):Prop:=
match x with
| true => True
| false => False
end.

(**
By using coercion [TRUE:bool >-> Sortclass] we identify [x :bool] with [TRUE x].  
*)

Coercion  TRUE:bool >-> Sortclass.

Lemma TrueTrue: true.
Proof.
simpl;auto.
Qed.

Lemma Contradiction: forall  (x:Prop), false -> x.
Proof.
intros;contradiction.
Qed.

(**  Operators &&,|| are standard Coq notations for boolean operators 'and' and 'or'. *)

Axiom Notfalse:negb false.
Axiom AndLeft: forall (x y:bool),x && y -> x.
Axiom AndRight:forall (x y:bool),x && y -> y.
Axiom SplitAnd:forall (x y:bool),x -> y -> x && y .
Axiom SplitOr: forall (x y:bool), ((x -> false)-> y) ->x || y.
Axiom LeftOr:  forall (x y:bool), x -> x || y.
Axiom RightOr: forall (x y:bool), y -> x || y.
Axiom OrCases: forall (x y:bool)(z:Prop), 
  x || y -> (x -> z) -> (y -> z) ->  z.
Axiom if_then_true: forall (S:Set)(x y:S)(b:bool), b ->(if b then x else y) = x.
Axiom if_then_false: forall (S:Set)(x y:S)(b:bool), (b -> false) -> (if b then x else y) = y.
Axiom Decide: forall (x:bool)(P:Prop), (x -> P) -> ((x -> false) -> P) -> P.
Axiom Notnegb:forall  (x:bool), x -> negb x ->false.
Axiom Absurd2:forall x y:bool, negb x -> x -> y.
Axiom ReplaceNotNot:forall  (x:bool), x -> negb (negb x).
Axiom NotReduct:forall  (x:bool), (x -> false) -> negb x.
Axiom ReplaceWithNotNot:forall  (x:bool), negb (negb x) -> x.
Axiom Contra:forall  (x y:bool), (negb x -> y) ->negb y -> x.
Axiom SplitOr2:forall (x y:bool), (negb x -> y) ->x || y.
Axiom Imply1:forall  (x y:bool), (negb x) || y -> x -> y.
Axiom Imply2:forall  (x y:bool), (x -> y) ->(negb x) || y.

Hint Resolve TrueTrue Notnegb: core.
Opaque TRUE.

(** Some tactics to simplify reasoning with booleans and propositions.  *)        

Ltac b_auto:=
   try
    match goal with
    | id1:?X,id2:~?X|- _ => absurd X;auto
    | id:(TRUE false) |- ?X3 =>
        apply Contradiction ; auto; b_auto
    | id0:(?X1 -> TRUE ?X2),id1:?X1 |- _ =>
        cut (TRUE X2); [ intro; clear id0; b_auto | apply id0; apply id1 ]
    | id0:(TRUE ?X1 -> ?X2),id1:TRUE ?X1 |- _ =>
        cut X2; [ intro; clear id0; b_auto | apply id0; apply id1 ]
    | id0:(TRUE ?X1 -> TRUE ?X2-> ?X3),id1:TRUE ?X1 |- _ =>
        cut (TRUE X2 -> X3); [ intro; clear id0; b_auto | intro;apply id0; auto ]
    | id0:(TRUE ?X1 -> TRUE ?X2-> ?X3),id1:TRUE ?X2 |- _ =>
        cut (TRUE X1 -> X3); [ intro; clear id0; b_auto | intro;apply id0; auto ]
    | id:(TRUE (andb ?X1 ?X2)) |-  _ =>
        cut (TRUE X1); [ intro | apply AndLeft with X2; apply id ];
         cut (TRUE X2);
         [ intro; clear id; b_auto | apply AndRight with X1; apply id ]
    | id:(TRUE (orb ?X1 ?X2)) |- (TRUE ?X3) =>
        apply OrCases with (x:=X1) (y:=X2) (z:= X3); auto;clear id; b_auto
    | id:(TRUE (orb ?X1 ?X2) -> TRUE ?X3) |- _ =>
        cut (TRUE X2 ->TRUE  X3);
         [ cut (TRUE X1 -> TRUE X3);
            [ intro; clear id; b_auto
            | intro; apply id; apply LeftOr; auto ]
         | intro; apply id; apply RightOr; auto ]
    |  |- (TRUE (orb _ _)) => apply SplitOr; b_auto
    |  |- (TRUE (andb _ _)) => apply SplitAnd; b_auto
    | id0:(?X1 -> TRUE ?X2),id1:?X1 |- _ =>
        cut (TRUE X2); [ intro; clear id0; b_auto | apply id0; apply id1 ]
    | id:(TRUE (andb ?X1 ?X2) ->?X3) |- _ =>
        cut (TRUE X1 -> TRUE X2 -> X3);
         [ intro; clear id; b_auto
         | intros; apply id;apply SplitAnd;auto ]
    | id:(TRUE (andb ?X1 ?X2) ->?X3->?X4) |- _ =>
        cut (TRUE X1 -> TRUE X2 -> X3->X4);
         [ intro; clear id; b_auto
         | intros; apply id; [apply SplitAnd;auto|auto ]]
    |  |- _ => eauto
    end.
 Ltac b_auto2:=
   b_auto;
   try
    match goal with
    | id:(TRUE (orb ?X1 ?X2)) |- ?X3 =>
        apply OrCases with (x:=X1) (y:=X2) (z:= X3); auto;clear id; b_auto2
    | id:(TRUE (orb ?X1 ?X2) -> ?X3) |- _ =>
        cut (TRUE X2 -> X3);
         [ cut (TRUE X1 -> X3);
            [ intro; clear id; b_auto2
            | intro; apply id; apply LeftOr; auto]
         | intro; apply id; apply RightOr; auto]
    end.

Ltac b_auto3:=
   try
    match goal with
    | id1:?X,id2:~?X|- _ => absurd X;auto
    | id:(TRUE false) |- ?X3 =>
        apply Contradiction ; auto; b_auto3
    |  |- (TRUE (negb _)) =>
        apply NotReduct; intro; b_auto3
    | id0:(?X1 -> TRUE ?X2),id1:?X1 |- _ =>
        cut (TRUE X2); [ intro; clear id0; b_auto3 | apply id0; apply id1 ]
    | id0:(TRUE ?X1 -> ?X2),id1:TRUE ?X1 |- _ =>
        cut X2; [ intro; clear id0; b_auto3 | apply id0; apply id1 ]
    | id0:(TRUE ?X1 -> TRUE ?X2-> ?X3),id1:TRUE ?X1 |- _ =>
        cut (TRUE X2 -> X3); [ intro; clear id0; b_auto3 | intro;apply id0; auto ]
    | id0:(TRUE ?X1 -> TRUE ?X2-> ?X3),id1:TRUE ?X2 |- _ =>
        cut (TRUE X1 -> X3); [ intro; clear id0; b_auto3 | intro;apply id0; auto ]
    | id:(TRUE (negb (negb ?X1)) -> ?X2) |- ?X3 =>
        cut (TRUE X1 -> X2);
         [ intro; clear id; b_auto3
         | intro; apply id; apply ReplaceNotNot; auto ]
    | id:(TRUE (negb ?X1) -> TRUE (false)) |- _ =>
        cut (TRUE X1);
         [ intro; clear id; b_auto3 | apply Contra with (x:=X1)(y:=false);
         auto;apply Notfalse]
    | id:(TRUE (negb (negb ?X1))) |- _ =>
        cut (TRUE X1);
         [ intro; clear id; b_auto3 | apply ReplaceWithNotNot; apply id ]
    | id:(TRUE (negb ?X1)) |- _ =>
        cut (TRUE X1 -> TRUE false);
         [ intro; clear id; b_auto3 | apply Absurd2 with (x:=X1)(y:=false);
         apply id;auto]
    | id:(TRUE ?X3 -> TRUE (negb ?X1)) |- _ =>
        cut (TRUE X3 -> TRUE X1 -> TRUE false);
         [ intro; clear id; b_auto3
         | intro; apply Absurd2 with (x:=X1)(y:=false);
          apply id; auto]
    | id:(TRUE (andb ?X1 ?X2)) |-  _ =>
        cut (TRUE X1); [ intro | apply AndLeft with X2; apply id ];
         cut (TRUE X2);
         [ intro; clear id; b_auto3 | apply AndRight with X1; apply id ]
    | id:(TRUE (orb (negb ?X1) ?X2)) |- _ =>
        cut (TRUE X1 -> TRUE X2);
         [ intro; clear id; b_auto3 | apply Imply1; apply id]
    | id:(TRUE (orb (negb ?X1) ?X2))->?X3 |- _ =>
        cut ((TRUE X1 -> TRUE X2) ->X3);
         [ intro; clear id; b_auto3 | intros; apply id;b_auto3]
    | id:?X3->(TRUE (orb (negb ?X1) ?X2)) |- _ =>
        cut (X3->(TRUE X1 -> TRUE X2));
         [ intro; clear id; b_auto3 | intro;
         cut (TRUE (orb (negb X1) X2));b_auto3]
    | id:(TRUE (orb ?X1 ?X2)) |- (TRUE ?X3) =>
        apply OrCases with (x:=X1) (y:=X2) (z:= X3); auto;clear id; b_auto3
    | id:(TRUE (orb ?X1 ?X2) -> TRUE ?X3) |- _ =>
        cut (TRUE X2 ->TRUE  X3);
         [ cut (TRUE X1 -> TRUE X3);
            [ intro; clear id; b_auto3
            | intro; apply id; apply LeftOr; auto ]
         | intro; apply id; apply RightOr; auto ]
    |  |- (TRUE (orb (negb _) _)) => apply Imply2; b_auto3
    |  |- (TRUE (orb _ _)) => apply SplitOr; b_auto3

    |  |- (TRUE (andb _ _)) => apply SplitAnd; b_auto3
    | id0:(?X1 -> TRUE ?X2),id1:?X1 |- _ =>
        cut (TRUE X2); [ intro; clear id0; b_auto3 | apply id0; apply id1 ]
    | id:(TRUE (andb ?X1 ?X2) ->?X3) |- _ =>
        cut (TRUE X1 -> TRUE X2 -> X3);
         [ intro; clear id; b_auto3
         | intros; apply id;apply SplitAnd;auto ]
    | id:(TRUE (andb ?X1 ?X2) ->?X3->?X4) |- _ =>
        cut (TRUE X1 -> TRUE X2 -> X3->X4);
         [ intro; clear id; b_auto3
         | intros; apply id; [apply SplitAnd;auto|auto ]]
    | id:(TRUE (negb ?X1) -> ?X2) |- _ =>
        cut ((TRUE X1 -> TRUE false) -> X2);
         [ intro; clear id; b_auto3
         | intro; apply id; apply NotReduct; auto ]
    |  |- _ => eauto
    end.

Ltac b_auto4:=
   b_auto3;
   try
    match goal with
    | id:(TRUE (orb ?X1 ?X2)) |- ?X3 =>
        apply OrCases with (x:=X1) (y:=X2) (z:= X3); auto;clear id; b_auto4
    | id:(TRUE (orb ?X1 ?X2) -> ?X3) |- _ =>
        cut (TRUE X2 -> X3);
         [ cut (TRUE X1 -> X3);
            [ intro; clear id; b_auto4
            | intro; apply id; apply LeftOr; auto]
         | intro; apply id; apply RightOr; auto]
    end.


Ltac b_intros:=
  b_auto;
  try
  match goal with
    |  |- (_ -> _) => intro; b_intros
  end.

Ltac b_intros2:=
   b_auto2;
   try
   match goal with
    |  |- (_ -> _) => intro; b_intros2
   end.

Ltac b_intros3:=
  b_auto3;
  try
  match goal with
    |  |- (_ -> _) => intro; b_intros3
  end.

Ltac b_intros4:=
  b_auto4;
  try
  match goal with
    |  |- (_ -> _) => intro; b_intros4
  end.

Ltac T_tail A:=
match A with
       | (?x1 ?x) => constr :x
       | (?x1 ?x2 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x) => constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x) => 
        constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x) =>
        constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x) => 
        constr :x
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x) => 
        constr :x
       | _ => A 
end.  

Ltac T_head A:=
match A with
       | (?x1 _) => constr :x1
       | (?x1 ?x2 _) => constr :(x1 x2)
       | (?x1 ?x2 ?x3 _) => constr :(x1 x2 x3)
       | (?x1 ?x2 ?x3 ?x4 _) => constr :(x1 x2 x3 x4)
       | (?x1 ?x2 ?x3 ?x4 ?x5 _) => constr :(x1 x2 x3 x4 x5)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 _) => constr :(x1 x2 x3 x4 x5 x6)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 _) => constr :(x1 x2 x3 x4 x5 x6 x7)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 _) => constr :(x1 x2 x3 x4 x5 x6 x7 x8)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 _) => 
        constr :(x1 x2 x3 x4 x5 x6 x7 x8 x9)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 _) => 
        constr :(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 _) =>
        constr :(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 _) => 
        constr :(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
       | (?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 _) => 
        constr :(x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
       | _ => A 
end.

Ltac b_rew  A :=
  match  A with
   | if ?x then ?a else ?b =>
      let t:=(type of a) in
      match goal with
       | id:(TRUE x -> TRUE false) |- _ =>
       try (rewrite  if_then_false with t a b x)
       | id:(TRUE x) |- _ =>
       try (rewrite  if_then_true with t a b x)
       | |- _ => b_rew a;b_rew b
      end  
   | ?X -> ?Y => b_rew X; b_rew Y
   | _ =>
     let T := T_tail A in
     let H := T_head A in
     match  A with
      | T => auto
      | _ => b_rew T;b_rew H
     end
 end.
   
Ltac b_rewrite:=
   try
    match goal with
    |  |- ?A => b_rew A
    end.

Ltac b_rew0  A :=
  match  A with
   | if ?x then ?a else ?b =>
      match goal with
       | id:(TRUE x -> TRUE false) |- _ => (pose x)
       | id:(TRUE x) |- _ =>(pose x)
       | |- _ => b_rew0 a;b_rew0 b
      end  
   | ?X -> ?Y => b_rew0 X; b_rew0 Y
   | _ =>
     let T := T_tail A in
     let H := T_head A in
     match  A with
      | T => auto
      | _ => b_rew0 T;b_rew0 H
     end
 end.
   
Ltac b_rewrite0:=
   try
    match goal with
    |  |- ?A => b_rew0 A
    end.
