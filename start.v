Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.


(* RF definitions *)
Inductive lval : Type :=
  | Var (x : string)
  | Deref (w : lval).

Inductive value : Type :=
  | Unit
  | Int (n : nat)
  | OwnRef
  | BorrowRef.

Inductive partal_value : Type :=
  | Undefined
  | Defined (v : value).

Inductive term : Type :=
  (* t1 ; t2 *)
  | Seq (t1 t2 : term)
  (* {t} *)
  | Block (t : term)
  (* let mut x = t *)
  | Declaration (x : string) (t : term)
  (* w = t *)
  | Assignment (w : lval) (t : term)
  (* box t *)
  | HeapAlloc (t : term)
  (* &w *)
  | Borrow (w : lval)
  (* &mut w *)
  | MutBorrow (w : lval)
  (* w *)
  | Move (w : lval)
  (* w.copy() *)
  | Copy (w : lval)
  (* v *)
  | Value (v : value).

Inductive type : Type :=
  | TUnit
  | TInt
  | TBorrow
  | TMutBorrow
  | TBox.

Inductive partal_type :=
  | PTDefined
  | PTPartalBox
  | PTUndefined.


(* notation for parsing *)
(*
Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (e custom com at level 100) : com_scope.
Notation "'e'" := (Value Unit) (in custom com at level 0) : com_scope.
Notation "t1 ; t2" := (Seq t1 t2) (in custom com at level 0) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'let' 'mut' x = t" := (Declaration x t) (
  in custom com at level 0) : com_scope.
Notation "{ t }" := (Block t) (in custom com at level 1) : com_scope.
Open Scope com_scope.
Unset Printing Notations.
Check <{ let mut y = e }>.

Unset Printing Notations.
Set Printing Coercions.
Print test_parser1.
Set Printing Notations.
Unset Printing Coercions.
*)

(* state *)

(* stuff for maps from Maps.v*)
Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
                    fun x' => if String.eqb x x' then v else m x'.

(* map notation *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition example_store :=
  ( "x" !-> Int 1;
    "y" !-> Int 2;
    _ !-> Unit 
  ).

Definition store := total_map value.

Fixpoint loc (st : store) (w : lval) : value :=
  match w with 
  | Deref w' => loc st w'
  | Var str => st str
  end.

Compute loc example_store (Var "x"%string).

(* playgound *)

(* {1} *)
Check Block (Value (Int 1)).

(* 

{
  let mut x = box 0; 
  {
    let mut y = &mut x;
    *y = box 1;
  }; 
  let mut z = x;
} 
*)
Check Block (Seq
  (* let mut x = box 0 *)
  (Declaration "x" (HeapAlloc (Value (Int 0))))
  (Seq
    (Block (Seq 
      (* let mut y = &mut x *)
      (Declaration "y" (MutBorrow (Var "x"))) 
      (Seq 
      (* *y = box 1 *)
        (Assignment (Deref (Var "y")) (HeapAlloc (Value (Int 1)))) 
        (Value Unit)
      )
    ))
    (Seq
      (* let mut z = x *)
      (Declaration "z" (Move (Var "x")))
      (Value Unit)
    )
  )
).
