Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.

(* locations are strings *)
Definition location := string.
Definition lifetime := string.

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
  | TBlock (t : term) (lf : lifetime)
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
Definition store := list (location * (partial_value * lifetime)).

Definition s_alloc (st : store) (l : location) (pv_l : partial_value * lifetime) 
  : store :=
  cons (l, pv_l) st.


Fixpoint s_in (st :store) (l : location) 
  : partial_value * lifetime :=
  match st with
  | nil => (PVUndefined, "global"%string)
  | ((cl, pv_l) :: tl)%list => if (eqb cl l) then pv_l else s_in tl l
  end.


Compute s_alloc nil "lx"%string (PVDefined VUnit, "l"%string).

(* stuff for maps from Maps.v*)
(*
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

*)


(* 
   store : locations -> (partial_value * lifetimes)
   locations : string
   lifetimes : string
   locations and lifetimes maybe should not be raw strings
 *)
(* Definition store := total_map (partial_value * lifetime). *)


Definition example_store := (
  ("x"%string, (PVDefined (VInt 1),         "l_l"%string)) ::
  ("p"%string, (PVDefined (VBorrowRef "x"), "l_m"%string)) ::
  ("d"%string, (PVDefined (VBorrowRef "p"), "l_f"%string)) ::
  ("t"%string, (PVDefined (VBorrowRef "d"), "l_a"%string)) ::
    nil
  )%list.

(* SEMANTICS *)

Inductive loc : store -> lval -> location -> Prop :=
  | Loc_Var : forall (st : store) (var_loc : string), 
      ~ (fst (s_in st var_loc)) = PVUndefined ->
      loc st (LVar var_loc) var_loc
  | Loc_Deref : 
      forall (st : store) (l lw: location) (w : lval),
      (
        fst (s_in st lw) = PVDefined (VBorrowRef l) \/
        fst (s_in st lw) = PVDefined (VOwnRef l)
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
      s_in st l = pv_l ->
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

Example read_ex5 :
  read nil (LVar "x"%string) (PVUndefined, "global"%string).
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
      fst (s_in st' l) = pv ->
      loc st w l ->
      write st w pv st'.


Definition es_1 :=
  ( ("x"%string, (PVDefined (VInt 0),         "lifetime_l"%string)) ::
    nil
  )%list.

Definition es_1' :=
  ( ("x"%string, (PVDefined (VInt 1),         "lifetime_l"%string)) ::
    nil
  )%list.

Example write_ex1 :
  write nil (LVar "x"%string) (PVDefined (VInt 0)) es_1.
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
  ("x"%string, (PVDefined (VInt 1),         "lifetime_l"%string)) ::
  ("p"%string, (PVDefined (VBorrowRef "x"), "lifetime_g"%string)) ::
  nil
  )%list.
Definition es_3 :=
  ( 
  ("x"%string, (PVDefined (VInt 2),         "lifetime_l"%string)) ::
  ("p"%string, (PVDefined (VBorrowRef "x"), "lifetime_g"%string)) ::
  nil
  )%list.

Example write_ex3 :
  write es_2 (LDeref (LVar "p"%string)) (PVDefined (VInt 2)) es_3.
Proof.
  apply Write with (l := "x"%string).
  + simpl. reflexivity.
  + loc_deref "p"%string.
Qed.


(* IMPORTANT: To implement drop correctly I fear we may have to use a non function 
   version of a store *)


Fixpoint remove_location (st : store) (l : location) : store :=
  match st with
  | nil => nil
  | (hd :: tl)%list => if (eqb l (fst hd))%string 
      then remove_location tl l 
      else (hd :: remove_location tl l)%list
  end.

Fixpoint remove_locations (st : store) (l : list location) : store :=
  match l with
  | nil => st
  | cons hd tl => remove_locations (remove_location st hd) tl
  end.

Fixpoint collect_in_scope (st : store) (lf : lifetime) (lst : list location)
  : list location :=
  match st with 
  | nil => lst
  | ((l, (pv, clf)) :: tl)%list => if (eqb clf lf)%string
      then collect_in_scope tl lf (l :: lst)%list
      else collect_in_scope tl lf lst
  end.

Fixpoint collect_pvs (st : store) (lst : list location) (pvs : list partial_value) 
  : list partial_value :=
  match lst with 
  | nil => pvs
  | (l :: tl)%list => collect_pvs st tl (fst (s_in st l) :: pvs)%list
  end.

Inductive drop : store -> list partial_value -> store -> Prop :=
  | D_nil : forall (st : store),
      drop st nil st
  | D_cons_other : forall (st : store) (pv : partial_value) (tl : list partial_value),
      (forall (l : location), (pv <> PVDefined (VOwnRef l))) ->
      drop st (cons pv tl) st
  | D_cons_own : forall (st1 st2 st3 : store)
      (tl : list partial_value) (l l_own : location),
      fst (s_in st1 l_own) = (PVDefined (VOwnRef l)) ->
      st2 = remove_location st1 l_own ->
      drop st2 (cons (fst (s_in st1 l)) tl) st3  ->
      drop st1 (cons (PVDefined (VOwnRef l)) tl) st2.

Definition drop_ex1_st1 : store :=
  (
    ("lx"%string, ((PVDefined (VInt 1)),"l"%string)) ::
    ("lp"%string, ((PVDefined (VOwnRef "lx"%string)),"m"%string)) ::
    nil
  )%list.

Definition drop_ex1_st2 : store :=
  (
    ("lx"%string, ((PVDefined (VInt 1)),"l"%string)) ::
    nil
  )%list.

Example drop_ex1 : drop drop_ex1_st1 
  (collect_pvs drop_ex1_st1 ("lp"%string :: nil)%list nil) 
  drop_ex1_st2.
Proof. simpl. apply D_cons_own with (st3 := drop_ex1_st2) (l_own := "lp"%string).
+ reflexivity.
+ reflexivity.
+ simpl. apply D_cons_other. unfold not. intros l H. injection H as H1. discriminate.
Qed.


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
    fst (s_in st1 n) = PVUndefined ->
    st2 = cons (n, (PVDefined v, "global"%string)) st1 ->
    (THeapAlloc (TValue v), st1) --> (TValue (VOwnRef n), st2) | slf
| R_Borrow : forall (w : lval) (lw : location) (slf : lifetime) (st : store),
    loc st w lw ->
    (TBorrow w, st) --> (TValue (VBorrowRef lw), st) | slf
| R_MutBorrow : forall (w : lval) (lw : location) (slf : lifetime) (st : store),
    loc st w lw ->
    (TMutBorrow w, st) --> (TValue (VOwnRef lw), st) | slf
| R_Assign : forall (st1 st2 st3 : store) 
    (w : lval) (v2 : value) (pv1 : partial_value * lifetime) (slf : lifetime),
    read st1 w pv1 ->
    drop st1 (fst pv1 :: nil)%list st2 ->
    write st2 w (PVDefined v2) st3 ->
    (TAssignment w (TValue v2), st1) --> (TValue VUnit, st3) | slf
| R_Declare : forall (v : value) (lx : location) (x : string) (slf : lifetime) (st1 st2 : store),
    st2 = cons (lx, (PVDefined v, slf)) st1 ->
    (TDeclaration x (TValue v), st1) --> (TValue VUnit, st2) | slf
| R_Seq : forall (st1 st2 : store) (v : value) (t : term) (slf : lifetime),
    drop st1 (PVDefined v :: nil)%list st2 ->
    (TSeq (TValue v) t, st1) --> (t, st2) | slf
| R_BlockA : forall (st1 st2 : store) (l_lf m_lf : lifetime) (t1 t2 : term),
    (t1, st1) --> (t2, st2) | m_lf ->
    (TBlock t1 m_lf, st1) --> (TBlock t2 m_lf, st2) | l_lf
| R_BlockB : forall (st1 st2 : store) (l_lf m_lf : lifetime) (v : value),
    drop st1 (collect_pvs st1 (collect_in_scope st1 m_lf nil) nil) st2 ->
    (TBlock (TValue v) m_lf, st1) --> (TValue v, st2) | l_lf
| R_Sub_HeapAlloc : forall (st1 st2 : store) (l_lf : lifetime) (t1 t2 : term),
    (t1,st1) --> (t2,st2) | l_lf ->
    (THeapAlloc t1, st1) --> (THeapAlloc t2, st2) | l_lf
| R_Sub_Seq : forall (st1 st2 : store) (l_lf : lifetime) (t1 t2 t3 : term),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TSeq t1 t2, st1) --> (t3, st2) | l_lf
where " t '-->' t' '|' l " := (step l t t').

(* figuring out R_Sub *)
Open Scope list.
Open Scope string.

Definition r_sub1_st := ("y", (PVDefined (VInt 1), "l_lf")) :: nil.
Example r_sub1: (THeapAlloc (TCopy (LVar "y")),r_sub1_st) --> 
  (THeapAlloc (TValue (VInt 1)) ,r_sub1_st) | "l_lf".
Proof.
  apply R_Sub_HeapAlloc.
  apply R_Copy with (lf := "l_lf").
  + apply Read with (l := "y").
    - reflexivity.
    - loc_var.
Qed.

Definition r_sub2_st  := ("y", (PVDefined (VInt 1), "l_lf")) :: nil.
Definition r_sub2_st' := ("y", (PVDefined (VInt 2), "l_lf")) :: nil.
Example r_sub2: 
  (TSeq (TAssignment (LVar "y") (TValue (VInt 2))) (TValue VUnit)
  ,r_sub2_st) 
  --> 
  (TSeq (TValue VUnit) (TValue VUnit) ,r_sub2_st') | "l_lf".
Proof.
  apply R_Sub_Seq. apply R_Assign with (st2 := r_sub2_st) (pv1 := (PVDefined (VInt 1), "l_lf")).
  + apply Read with (l := "y").
    - simpl. reflexivity.
    - loc_var.
  + simpl. apply D_cons_other. intros l. intros H. injection H as H1. discriminate.
  + apply Write with (l := "y").
    - simpl. reflexivity.
    - loc_var.
  Qed.

(* worked example 1 *)

Definition we1_0 : (term * store) :=
  (
  TBlock (
  TSeq 
    (TDeclaration "x"%string (TValue (VInt 1)))
    (
    TSeq
      (TDeclaration "y"%string (THeapAlloc (TCopy (LVar "x"%string))))
      (TBlock (
      TSeq 
        (TDeclaration "z"%string (THeapAlloc (TValue (VInt 0))))
        (
        TSeq
          (TAssignment (LVar "y"%string) (TBorrow (LVar "z"%string)))
          (
          TSeq
            (TAssignment (LVar "y"%string) (TMove (LVar "z"%string)))
            (
            TSeq
              (TMove (LDeref (LVar "y")))
              (TValue VUnit)
            )
          )
        )
      ) "m_lf"%string)
    )
  ) "l_lf"%string
  ,
  nil
  ).

Definition we1_1 : (term * store) :=
  (
  TBlock (
      (TBlock (
      TSeq 
        (TDeclaration "z"%string (THeapAlloc (TValue (VInt 0))))
        (
        TSeq
          (TAssignment (LVar "y"%string) (TBorrow (LVar "z"%string)))
          (
          TSeq
            (TAssignment (LVar "y"%string) (TMove (LVar "z"%string)))
            (
            TSeq
              (TMove (LDeref (LVar "y")))
              (TValue VUnit)
            )
          )
        )
      ) "m_lf"%string)
  ) "l_lf"%string
  ,
  (
  ("lx"%string, (PVDefined (VInt 1), "l_lf"%string)) ::
  ("ly"%string, (PVDefined (VOwnRef "l1"%string), "l_lf"%string)) ::
  ("l1"%string, (PVDefined (VInt 1), "global"%string)) ::
  nil
  )%list
  ).

Example we1_step_0_1 : we1_0 --> we1_1 | "l_lf"%string.
Proof.
  apply R_BlockA.

