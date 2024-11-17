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



(* state *)

(* locations are strings *)
Definition location := string.
Definition lifetime := string.
Definition store' := list (location * (partial_value * lifetime)).

Definition s_alloc (st : store') (l : location) (pv_l : partial_value * lifetime) 
  : store' :=
  cons (l, pv_l) st.

Compute s_alloc nil "lx"%string (PVDefined VUnit, "l"%string).

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



(* 
   store : locations -> (partial_value * lifetimes)
   locations : string
   lifetimes : string
   locations and lifetimes maybe should not be raw strings
 *)
Definition store := total_map (partial_value * lifetime).


Definition example_store :=
  ( "x" !-> (PVDefined (VInt 1),         "l_l"%string);
    "p" !-> (PVDefined (VBorrowRef "x"), "l_m"%string);
    "d" !-> (PVDefined (VBorrowRef "p"), "l_f"%string);
    "t" !-> (PVDefined (VBorrowRef "d"), "l_a"%string);
    _ !-> (PVUndefined, ""%string)
  ).

(* SEMANTICS *)

(*
   loc {
     "x" |-> <   1    >_{m},
     "p" |-> <bref "x">_{n}
   }, x = "x"

   loc {
     "x" |-> <   1    >_{m},
     "p" |-> <bref "x">_{n}
   }, *p = "x"

   loc {
     "x" |-> <   1    >_{m},
     "p" |-> <bref "x">_{n}
     "d" |-> <bref "p">_{n}
   }, *d = "p"

   loc {
     "x" |-> <   1    >_{m},
     "p" |-> <bref "x">_{n}
     "d" |-> <bref "p">_{n}
   }, **d = "x"
*)
Inductive loc : store -> lval -> location -> Prop :=
  | Loc_Var : forall (st : store) (var_loc : string), 
      ~ (fst (st var_loc)) = PVUndefined ->
      loc st (LVar var_loc) var_loc
  | Loc_Deref : 
      forall (st : store) (l lw: location) (w : lval),
      (
        fst (st lw) = PVDefined (VBorrowRef l) \/
        fst (st lw) = PVDefined (VOwnRef l)
      ) ->
      loc st w lw ->
      loc st (LDeref w) l.

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
  apply Loc_Deref with (lw := "p"%string). 
  + simpl. left. reflexivity.
  + apply Loc_Var. intros H. simpl in H. discriminate.
Qed.

Ltac loc_var := apply Loc_Var; unfold not; intros H; discriminate.
Ltac loc_deref s := apply Loc_Deref with (lw := s); 
  simpl; try (left; reflexivity); try (right; reflexivity); try (loc_var).

Example loc_ex5 : loc example_store (LDeref (LVar "d"%string)) "p"%string.
Proof.
  loc_deref "d"%string.
Qed.

Example loc_ex6 : loc example_store (LDeref (LDeref (LVar "d"%string))) "x"%string.
Proof.
  apply Loc_Deref with (lw := "p"%string). 
  + simpl. left. reflexivity.
  + apply Loc_Deref with (lw := "d"%string).
    - simpl. left. reflexivity.
    - apply Loc_Var. intros H. discriminate.
Qed.

Example loc_ex6' : loc example_store (LDeref (LDeref (LVar "d"%string))) "x"%string.
Proof.
  loc_deref "p"%string. loc_deref "d"%string.
Qed.

Example loc_ex7 : 
  loc example_store (LDeref (LDeref (LDeref (LVar "t"%string)))) "x"%string.
Proof.
  loc_deref "p"%string. loc_deref "d"%string. loc_deref "t"%string.
Qed.

Example loc_ex8 : 
  loc example_store (LDeref (LVar "x"%string)) "x"%string.
Proof.
loc_deref "x"%string. Abort. (* we are stuck because x is not a ref*)

Inductive read: store -> lval -> partial_value * lifetime -> Prop :=
  | Read : forall (st : store) (w : lval) (pv_l : partial_value * lifetime) (l : location), 
      st l = pv_l ->
      loc st w l ->
      read st w pv_l.

Example read_ex1 :
  read example_store (LVar "x"%string) ((PVDefined (VInt 1)), "l_l"%string).
Proof.
  apply Read with (l := "x"%string). 
  + simpl. reflexivity.
  + loc_var.
Qed.

Example read_ex2 :
  read example_store (LVar "p"%string) ((PVDefined (VBorrowRef "x"%string)), "l_m"%string).
Proof.
  apply Read with (l := "p"%string). 
  + simpl. reflexivity.
  + loc_var.
Qed.

Example read_ex3 :
  read example_store (LDeref (LVar "p"%string)) ((PVDefined (VInt 1)), "l_l"%string).
Proof.
  apply Read with (l := "x"%string).
  + simpl. reflexivity.
  + loc_deref "p"%string.
Qed.

Example read_ex4 :
  read example_store (LDeref (LDeref (LVar "d"%string))) ((PVDefined (VInt 1)), "l_l"%string).
Proof.
  apply Read with (l := "x"%string).
  + simpl. reflexivity.
  + loc_deref "p"%string. loc_deref "d"%string.
Qed.

Definition es_empty :=
  ( _ !-> (PVUndefined, "global"%string)).

Example read_ex5 :
  read es_empty (LVar "x"%string) (PVUndefined, "global"%string).
Proof. 
  apply Read with (l := "x"%string).
  + simpl. reflexivity.
  + apply Loc_Var. intros H.
  simpl in H. Abort .
(* we are stuck because reads should not be about to return Undefined values*)


(* 
My first attempt at this in (loc st w l) was instead (loc st' w l) but apparently 
for write to succed the location l has to already be alocated in st.
*)
Inductive write: store -> lval -> partial_value -> store -> Prop :=
  | Write : forall (st st' : store) (pv : partial_value) (l : location) (w : lval),
      fst (st' l) = pv ->
      loc st w l ->
      write st w pv st'.


Definition es_1 :=
  ( "x" !-> (PVDefined (VInt 0),         "lifetime_l"%string);
    _ !-> (PVUndefined, "global"%string)
  ).

Definition es_1' :=
  ( "x" !-> (PVDefined (VInt 1),         "lifetime_l"%string);
    _ !-> (PVUndefined, "global"%string)
  ).

Example write_ex1 :
  write es_empty (LVar "x"%string) (PVDefined (VInt 0)) es_1.
Proof.
  apply Write with (l := "x"%string).
  + simpl. reflexivity.
  + apply Loc_Var. intros H. simpl in H. 
  Abort.
    (* this fails because x was not defined in st*)

Example write_ex2 :
  write es_1 (LVar "x"%string) (PVDefined (VInt 1)) es_1'.
Proof.
  apply Write with (l := "x"%string).
  - simpl. reflexivity.
  - loc_var.
  Qed.


Definition es_2 :=
  ( 
  "x" !-> (PVDefined (VInt 1),         "lifetime_l"%string);
  "p" !-> (PVDefined (VBorrowRef "x"), "lifetime_g"%string);
  _ !-> (PVUndefined, "global"%string)
  ).
Definition es_3 :=
  ( 
  "x" !-> (PVDefined (VInt 2),         "lifetime_l"%string);
  "p" !-> (PVDefined (VBorrowRef "x"), "lifetime_g"%string);
  _ !-> (PVUndefined, ""%string)
  ).

Example write_ex3 :
  write es_2 (LDeref (LVar "p"%string)) (PVDefined (VInt 2)) es_3.
Proof.
  apply Write with (l := "x"%string).
  + simpl. reflexivity.
  + loc_deref "p"%string.
Qed.


(* IMPORTANT: To implement drop correctly I fear we may have to use a non function 
   version of a store *)

Fixpoint drop_locations (st : store) (l : list location) : store :=
  match l with
  | nil => st
  | cons hd tl => t_update (drop_locations st tl) hd (PVUndefined, "global"%string)
  end.


Reserved Notation " t '-->' t' '|' l " (at level 40).

Inductive step : lifetime -> (term * store) -> (term * store) -> Prop :=
| R_Copy : forall (w : lval) (v : value) (lf slf : lifetime) (st : store),
    read st w (PVDefined v, lf) ->
    (TCopy w, st) --> (TValue v, st) | slf
| R_Move : forall (w : lval) (v : value) (lf slf : lifetime) (st1 st2 : store),
    read st1 w (PVDefined v, lf) ->
    write st1 w PVUndefined st2 ->
    (TMove w, st1) --> (TValue v, st2) | slf
| R_Box : forall (v : value) (n : location) (slf : lifetime) (st1 st2 : store),
    fst (st1 n) = PVUndefined ->
    st2 = t_update st1 n (PVDefined v, "global"%string) ->
    (THeapAlloc (TValue v), st1) --> (TValue (VOwnRef n), st2) | slf
| R_Borrow : forall (w : lval) (lw : location) (slf : lifetime) (st : store),
    loc st w lw ->
    (TBorrow w, st) --> (TValue (VBorrowRef lw), st) | slf
| R_MutBorrow : forall (w : lval) (lw : location) (slf : lifetime) (st : store),
    loc st w lw ->
    (TMutBorrow w, st) --> (TValue (VOwnRef lw), st) | slf
| R_Declare : forall (v : value) (lx : location) (x : string) (slf : lifetime) (st1 st2 : store),
    st2 = t_update st1 lx (PVDefined v, slf) ->
    (TDeclaration x (TValue v), st1) --> (TValue VUnit, st2) | slf
where " t '-->' t' '|' l " := (step l t t').



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
