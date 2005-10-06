Set Implicit Arguments.
Unset Strict Implicit.
Require Import Bool.

(**************************************************************************************************)
(*      Parameter TRUE could be defined explicitely,                                              *) 
(*     so that inhabited (TRUE x) corresponds to truth                                            *)        
(*     Due to coercion we can write x instead of (TRUE x)                                         *)        
(**************************************************************************************************)

Parameter TRUE:bool -> Prop.
Coercion  TRUE:bool >-> Sortclass.

(**************************************************************************************************)
(*  Following axioms easely shown to be compatible with Coq                                       *)        
(*  Operators &&,||, negb are standart Coq boolean operators                                      *)
(**************************************************************************************************)

Axiom AndLeft:forall (x y:bool),x && y -> x.
Axiom AndRight:forall (x y:bool),x && y -> y.
Axiom SplitAnd:forall (x y:bool),x -> y -> x && y .
Axiom TrueTrue:true.
Axiom Notfalse:negb false.
Axiom Decide:forall (x:bool)(P:Prop),
 (x -> P) -> ((x -> false) -> P) -> P.
Axiom Contradiction:forall  (x:Prop), false -> x.
Axiom ReplaceNotNot:forall  (x:bool), x -> negb (negb x).
Axiom Absurd2:forall x y:bool, negb x -> x -> y.
Axiom NotReduct:forall  (x:bool), (x -> false) -> negb x.
Axiom ReplaceWithNotNot:forall  (x:bool), negb (negb x) -> x.
Axiom Contra:forall  (x y:bool), (negb x -> y) ->negb y -> x.
Axiom LeftOr:forall  (x y:bool), x -> x || y.
Axiom RightOr:forall (x y:bool), y -> x || y.
Axiom SplitOr:forall (x y:bool), (negb x -> y) ->x || y.
Axiom OrCases:forall (x y:bool)(z:Prop), 
  x || y -> (x -> z) -> (y -> z) ->  z.
Axiom Imply1:forall  (x y:bool), (negb x) || y -> x -> y.
Axiom Imply2:forall  (x y:bool), (x -> y) ->(negb x) || y.
Axiom TrueEq:forall (x:bool), x -> x  = true .
Axiom FalseEq:forall (x:bool), (x -> false) -> x  = false .

(**************************************************************************************************)
(*  Tactics to simplify reasoning with booleans and propositions                                  *)        
(**************************************************************************************************)

Ltac b_auto:=
   try
    match goal with
    | id1:?X,id2:~?X|- _ => absurd X;auto
    | id:(TRUE false) |- ?X3 =>
        apply Contradiction ; auto; b_auto
    |  |- (TRUE (negb _)) =>
        apply NotReduct; intro; b_auto
    | id0:(?X1 -> TRUE ?X2),id1:?X1 |- _ =>
        cut (TRUE X2); [ intro; clear id0; b_auto | apply id0; apply id1 ]
    | id0:(TRUE ?X1 -> ?X2),id1:TRUE ?X1 |- _ =>
        cut X2; [ intro; clear id0; b_auto | apply id0; apply id1 ]
    | id0:(TRUE ?X1 -> TRUE ?X2-> ?X3),id1:TRUE ?X1 |- _ =>
        cut (TRUE X2 -> X3); [ intro; clear id0; b_auto | intro;apply id0; auto ]
    | id0:(TRUE ?X1 -> TRUE ?X2-> ?X3),id1:TRUE ?X2 |- _ =>
        cut (TRUE X1 -> X3); [ intro; clear id0; b_auto | intro;apply id0; auto ]
    | id:(TRUE (negb (negb ?X1)) -> ?X2) |- ?X3 =>
        cut (TRUE X1 -> X2);
         [ intro; clear id; b_auto
         | intro; apply id; apply ReplaceNotNot; auto ]
    | id:(TRUE (negb ?X1) -> TRUE (false)) |- _ =>
        cut (TRUE X1);
         [ intro; clear id; b_auto | apply Contra with (x:=X1)(y:=false);
         auto;apply Notfalse]
    | id:(TRUE (negb (negb ?X1))) |- _ =>
        cut (TRUE X1);
         [ intro; clear id; b_auto | apply ReplaceWithNotNot; apply id ]
    | id:(TRUE (negb ?X1)) |- _ =>
        cut (TRUE X1 -> TRUE false);
         [ intro; clear id; b_auto | apply Absurd2 with (x:=X1)(y:=false);
         apply id;auto]
    | id:(TRUE ?X3 -> TRUE (negb ?X1)) |- _ =>
        cut (TRUE X3 -> TRUE X1 -> TRUE false);
         [ intro; clear id; b_auto
         | intro; apply Absurd2 with (x:=X1)(y:=false);
          apply id; auto]
    | id:(TRUE (andb ?X1 ?X2)) |-  _ =>
        cut (TRUE X1); [ intro | apply AndLeft with X2; apply id ];
         cut (TRUE X2);
         [ intro; clear id; b_auto | apply AndRight with X1; apply id ]
    | id:(TRUE (orb (negb ?X1) ?X2)) |- _ =>
        cut (TRUE X1 -> TRUE X2);
         [ intro; clear id; b_auto | apply Imply1; apply id]
    | id:(TRUE (orb (negb ?X1) ?X2))->?X3 |- _ =>
        cut ((TRUE X1 -> TRUE X2) ->X3);
         [ intro; clear id; b_auto | intros; apply id;b_auto]
    | id:?X3->(TRUE (orb (negb ?X1) ?X2)) |- _ =>
        cut (X3->(TRUE X1 -> TRUE X2));
         [ intro; clear id; b_auto | intro;
         cut (TRUE (orb (negb X1) X2));b_auto]
    | id:(TRUE (orb ?X1 ?X2)) |- (TRUE ?X3) =>
        apply OrCases with (x:=X1) (y:=X2) (z:= X3); auto;clear id; b_auto
    | id:(TRUE (orb ?X1 ?X2) -> TRUE ?X3) |- _ =>
        cut (TRUE X2 ->TRUE  X3);
         [ cut (TRUE X1 -> TRUE X3);
            [ intro; clear id; b_auto
            | intro; apply id; apply LeftOr; auto ]
         | intro; apply id; apply RightOr; auto ]
    |  |- (TRUE (orb (negb _) _)) => apply Imply2; b_auto
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
    | id:(TRUE (negb ?X1) -> ?X2) |- _ =>
        cut ((TRUE X1 -> TRUE false) -> X2);
         [ intro; clear id; b_auto
         | intro; apply id; apply NotReduct; auto ]
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

Hint Resolve TrueTrue Notfalse:core.

Ltac and_intros:=
  b_auto;
  try
  match goal with
    |  |- (_ -> _) => intro; and_intros
  end.

Ltac and_intros2:=
   b_auto2;
   try
   match goal with
    |  |- (_ -> _) => intro; and_intros2
   end.
