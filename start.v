Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.


(* RF definitions *)
Inductive lval : Type :=
  | LVar (x : string)
  | LDeref (w : lval).

Inductive value : Type :=
  | VUnit
  | VInt (n : nat)
  | VOwnRef (s : string)
  | VBorrowRef (s : string).

Inductive partial_value : Type :=
  | PVUndefined
  | PVDefined (v : value).

Inductive term : Type :=
  (* t1 ; t2 *)
  | TSeq (t1 t2 : term)
  (* {t} *)
  | TBlock (t : term)
  (* let mut x = t *)
  | TDeclaration (x : string) (t : term)
  (* w = t *)
  | TAssignment (w : lval) (t : term)
  (* box t *)
  | THeapAlloc (t : term)
  (* &w *)
  | TBorrow (w : lval)
  (* &mut w *)
  | TMutBorrow (w : lval)
  (* w *)
  | TMove (w : lval)
  (* w.copy() *)
  | TCopy (w : lval)
  (* v *)
  | TValue (v : value).

Inductive type : Type :=
  | YUnit
  | YInt
  | YBorrow
  | YMutBorrow
  | YBox.

Inductive partial_type :=
  | PYDefined
  | PYPartalBox
  | PYUndefined.



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


(* locations are strings in this kind of map *)
Definition lifetime := string.
Definition location := string.

(* 
   store : locations -> (partial_value * lifetimes)
   locations : string
   lifetimes : string
   locations and lifetimes maybe should not be raw strings
 *)
Definition store := total_map (partial_value * lifetime).


Definition example_store :=
  ( "x" !-> (PVDefined (VInt 1),         "lifetime_l"%string);
    "p" !-> (PVDefined (VBorrowRef "x"), "lifetime_m"%string);
    "d" !-> (PVDefined (VBorrowRef "p"), "lifetime_f"%string);
    _ !-> (PVUndefined, ""%string)
  ).

(* SEMANTICS *)

Inductive loc : store -> lval -> location -> Prop :=
  | Loc_Var : forall (st : store) (var_loc : string), 
      ~ (fst (st var_loc)) = PVUndefined ->
      loc st (LVar var_loc) var_loc
  | Loc_Deref : 
      forall (st : store) (var_loc var_loc_interm : string) (w : lval),
      loc st w var_loc_interm ->
      loc st (LDeref w) var_loc.

Example loc_ex1 : loc example_store (LVar "x"%string) "x"%string.
Proof.
  apply Loc_Var. simpl. unfold not. intros H. discriminate.
Qed.

Example loc_ex2 : loc example_store (LVar "p"%string) "t"%string.
Proof.
  (* we are stuck because t != p*)
Abort.

Example loc_ex3 : loc example_store (LVar "y"%string) "y"%string.
Proof.
  apply Loc_Var. simpl. 
  (* we are stuck because there is no y in example_store *)
Abort.

Example loc_ex4 : loc example_store (LDeref (LVar "p"%string)) "x"%string.
Proof.
  apply Loc_Deref with (var_loc_interm := "p"%string). 
  apply Loc_Var. simpl. unfold not. intros H. discriminate H.
Qed.

Example loc_ex5 : loc example_store (LDeref (LVar "d"%string)) "p"%string.
Proof.
  apply Loc_Deref with (var_loc_interm := "d"%string). 
  apply Loc_Var. simpl. unfold not. intros H. discriminate H.
Qed.

Example loc_ex6 : loc example_store (LDeref (LDeref (LVar "d"%string))) "x"%string.
Proof.
  apply Loc_Deref with (var_loc_interm := "d"%string). 
  apply Loc_Deref with (var_loc_interm := "p"%string). 
  apply Loc_Var. simpl. unfold not. intros H. discriminate H.
Qed.

Compute example_store (loc example_store (Deref (Var "p"%string))).
Compute example_store (loc example_store (Deref (Var "x"%string))).

Fixpoint read (st : store) (w : lval) : partial_value :=
  match w with 
  | Var str => st str
  | Deref _ => st (loc st w)
  end.

Check t_update.

Compute read example_store (Var "x"%string).
Compute read example_store (Var "p"%string).
Compute read example_store (Deref (Var "p"%string)).
Compute read example_store (Deref (Deref (Var "p"%string))).

Fixpoint write (st : store) (w : lval) (v : partial_value) :=
  match w with 
  | Var str => t_update st str v
  | Deref _ => t_update st (loc st w) v
  end.

Compute read example_store (Var "x"%string).
Definition example_store' :=
  write example_store (Var "x"%string) (Defined (Int 2)).
Compute read example_store' (Var "x"%string).
Definition example_store'' :=
  write example_store (Deref (Var "p"%string)) (Defined (Int 3)).
Compute read example_store'' (Var "x"%string).
Definition example_store''' :=
  write example_store (Deref (Var "x"%string)) (Defined (Int 4)).
Compute read example_store''' (Var "x"%string).



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
