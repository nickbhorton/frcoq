Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.

Open Scope list.
Open Scope string.

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


Coercion VInt : nat >-> value.
Coercion LVar : string >-> lval.
Notation "'#' v" := (PVDefined v) (at level 0).
Notation "'##'" := (PVUndefined) (at level 0).
Notation "s1 ; s2" := (TSeq s1 s2) (at level 90, right associativity).
Notation "'<{' p '}>' lf" := (TBlock p lf) (at level 91, right associativity).

(* state *)
Definition store := list (location * (partial_value * lifetime)).

Definition s_push (st : store) (l : location) (pv_l : partial_value * lifetime) 
  : store :=
  cons (l, pv_l) st.

Fixpoint s_update (st : store) (l : location) (pv_l : partial_value * lifetime)
  : store :=
  match st with
  | nil => st
  | (current_l, current_pv_l) :: st' => if (current_l =? l) 
      then (current_l, pv_l) :: st'
      else (current_l, current_pv_l) :: (s_update st' l pv_l)
  end.

Fixpoint s_get (st :store) (l : location) 
  : partial_value * lifetime :=
  match st with
  | nil => (##, "global")
  | ((cl, pv_l) :: tl)%list => if (eqb cl l) then pv_l else s_get tl l
  end.


Definition st_tester := s_push nil "lx" (#VUnit, "l").
Compute s_update st_tester "lx" (#1, "l").
Compute s_update st_tester "no_loc" (#1, "l").

(* 
   store : locations -> (partial_value * lifetimes)
   locations : string
   lifetimes : string
   locations and lifetimes maybe should not be raw strings
 *)
(* Definition store := total_map (partial_value * lifetime). *)

Definition example_store :=
  ("x", (#1, "l_l")) ::
  ("p", (# (VBorrowRef "x"), "l_m")) ::
  ("d", (# (VBorrowRef "p"), "l_f")) ::
  ("t", (# (VBorrowRef "d"), "l_a")) :: nil.

(* SEMANTICS *)

Inductive loc : store -> lval -> location -> Prop :=
  | Loc_Var : forall (st : store) (var_loc : string), 
      ~ (fst (s_get st var_loc)) = ## ->
      loc st (LVar var_loc) var_loc
  | Loc_Deref : 
      forall (st : store) (l lw: location) (w : lval),
      (
        fst (s_get st lw) = # (VBorrowRef l) \/
        fst (s_get st lw) = # (VOwnRef l)
      ) ->
      loc st w lw ->
      loc st (LDeref w) l.

Ltac loc_var := apply Loc_Var; unfold not; intros H; discriminate.
Ltac loc_deref s := apply Loc_Deref with (lw := s); 
  simpl; try (left; reflexivity); try (right; reflexivity); try (loc_var).

Fixpoint find_loc (st : store) (s : string) : string :=
  match st with
  | nil => ""
  | (l,(# (VBorrowRef l'),_)) :: st' => if (l' =? s)%string
      then l
      else find_loc st' s
  | (l,(# (VOwnRef l'),_)) :: st' => if (l' =? s)%string
      then l
      else find_loc st' s
  | _ :: st' => find_loc st' s
  end.

Fixpoint deref_loc (st : store) (s : string) : string :=
  match st with
  | nil => ""
  | (l,(# (VBorrowRef l'),_)) :: st' => if (l =? s)%string
      then l'
      else deref_loc st' s
  | (l,(# (VOwnRef l'),_)) :: st' => if (l =? s)%string
      then l'
      else deref_loc st' s
  | _ :: st' => deref_loc st' s
  end.

Fixpoint deref_loc_repeat (st : store) (w : lval) : string :=
  match w with 
  | LVar s => s
  | LDeref o => deref_loc st (deref_loc_repeat st o)
  end.


Ltac auto_loc :=
  repeat match goal with
  | [ |- loc ?st (LVar ?x) ?y ] => loc_var
  | [ |- loc ?st (LDeref (LVar ?l)) ?y ] => loc_deref l
  | [ |- loc ?st ?a ?y ] => try loc_deref (find_loc st y)
  end.


Example loc_ex1 : loc example_store (LVar "x") "x".
Proof.
  apply Loc_Var. simpl. unfold not. intros H. discriminate.
Qed.

Example loc_ex1' : loc example_store (LVar "x") "x".
Proof.
  auto_loc.
Qed.

Example loc_ex2 : loc example_store (LVar "p") "t".
Proof.
  (* we are stuck because t != p*)
Abort.

Example loc_ex3 : loc example_store (LVar "y") "y".
Proof.
  apply Loc_Var. simpl. 
  (* we are stuck because there is no y in example_store *)
Abort.

Example loc_ex4 : loc example_store (LDeref (LVar "p")) "x".
Proof.
  apply Loc_Deref with (lw := "p"). 
  + simpl. left. reflexivity.
  + apply Loc_Var. intros H. simpl in H. discriminate.
Qed.

Example loc_ex4' : loc example_store (LDeref (LVar "p")) "x".
Proof.
  auto_loc.
Qed.


Example loc_ex5 : loc example_store (LDeref (LVar "d")) "p".
Proof.
  auto_loc.
Qed.

Example loc_ex6 : loc example_store (LDeref (LDeref (LVar "d"))) "x".
Proof.
  apply Loc_Deref with (lw := "p"). 
  + simpl. left. reflexivity.
  + apply Loc_Deref with (lw := "d").
    - simpl. left. reflexivity.
    - apply Loc_Var. intros H. discriminate.
Qed.

Example loc_ex6' : loc example_store (LDeref (LDeref (LVar "d"))) "x".
Proof.
  loc_deref "p". loc_deref "d".
Qed.

Example loc_ex6'' : loc example_store (LDeref (LDeref (LVar "d"))) "x".
Proof.
  auto_loc.
Qed.

Example loc_ex7 : 
  loc example_store (LDeref (LDeref (LDeref (LVar "t")))) "x".
Proof.
  loc_deref "p". loc_deref "d". loc_deref "t".
Qed.

Example loc_ex7' : 
  loc example_store (LDeref (LDeref (LDeref (LVar "t")))) "x".
Proof.
  auto_loc.
Qed.

Example loc_ex8 : 
  loc example_store (LDeref (LVar "x")) "x".
Proof.
loc_deref "x". Abort. (* we are stuck because x is not a ref*)

Example loc_ex8 : 
  loc example_store (LDeref (LVar "x")) "x".
Proof.
auto_loc. Abort. (* we are stuck because x is not a ref*)

Inductive read: store -> lval -> partial_value * lifetime -> Prop :=
  | Read : forall (st : store) (w : lval) (pv_l : partial_value * lifetime) (l : location), 
      s_get st l = pv_l ->
      loc st w l ->
      read st w pv_l.

Ltac read_rule s :=
      apply Read with (l := s);
      try (simpl; reflexivity); try auto_loc.

Ltac auto_read :=
  match goal with 
  | [ |- read ?st (LVar ?l) ?pv ] => read_rule l
  | [ |- read ?st ?d ?pv ] => read_rule (deref_loc_repeat st d)
  end.

Example read_ex1 :
  read example_store (LVar "x") (#1, "l_l").
Proof.
  apply Read with (l := "x"). 
  + simpl. reflexivity.
  + loc_var.
Qed.

Example read_ex1' :
  read example_store (LVar "x") (#1, "l_l").
Proof.
  auto_read.
Qed.

Example read_ex2 :
  read example_store (LVar "p") (#(VBorrowRef "x"), "l_m").
Proof.
  apply Read with (l := "p"). 
  + simpl. reflexivity.
  + loc_var.
Qed.

Example read_ex2' :
  read example_store (LVar "p") (#(VBorrowRef "x"), "l_m").
Proof.
  auto_read.
Qed.

Example read_ex3 :
  read example_store (LDeref (LVar "p")) ((#1), "l_l").
Proof.
  apply Read with (l := "x").
  + simpl. reflexivity.
  + loc_deref "p".
Qed.

Example read_ex3' :
  read example_store (LDeref (LVar "p")) ((#1), "l_l"). 
Proof.
  auto_read.
Qed.

Example read_ex4 :
  read example_store (LDeref (LDeref (LVar "d"))) ((#1), "l_l").
Proof.
  apply Read with (l := "x").
  + simpl. reflexivity.
  + loc_deref "p". loc_deref "d".
Qed.

Example read_ex4' :
  read example_store (LDeref (LDeref (LVar "d"))) ((#1), "l_l").
Proof.
  auto_read.
Qed.



Example read_ex5 :
  read nil "x" (##, "global").
Proof. 
  apply Read with (l := "x").
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
      fst (s_get st' l) = pv ->
      loc st w l ->
      write st w pv st'.

Ltac write_rule lv :=
  apply Write with (l := lv); 
    try (simpl; reflexivity);
    try auto_loc.

Ltac auto_write :=
  match goal with 
  | [ |- write ?st (LVar ?l) ?pv ?st' ] => write_rule l
  | [ |- write ?st ?w ?pv ?st' ] => write_rule (deref_loc_repeat st w)
  end.


Definition es_1 :=
  ("x", (#0,         "lifetime_l")) ::
    nil.

Definition es_1' := s_update es_1 "x" (#1, "lifetime_l").

Example write_ex1 :
  write nil (LVar "x") (#0) es_1.
Proof.
  apply Write with (l := "x").
  + simpl. reflexivity.
  + apply Loc_Var. intros H. simpl in H. 
  Abort.
    (* this fails because x was not defined in st*)

Example write_ex2 :
  write es_1 (LVar "x") (#1) es_1'.
Proof.
  apply Write with (l := "x").
  - simpl. reflexivity.
  - loc_var.
Qed.

Example write_ex2' :
  write es_1 (LVar "x") (#1) es_1'.
Proof. auto_write. Qed.


Definition es_2 :=
  ("x", (#1,         "lifetime_l")) ::
  ("p", (# (VBorrowRef "x"), "lifetime_g")) ::
  nil.

Definition es_3 := s_update es_2 "x" (#2, "lifetime_l").

Example write_ex3 :
  write es_2 (LDeref (LVar "p")) (#2) es_3.
Proof.
  apply Write with (l := "x").
  + simpl. reflexivity.
  + loc_deref "p".
Qed.

Example write_ex3' :
  write es_2 (LDeref (LVar "p")) (#2) es_3.
Proof.
  auto_write.
Qed.


(* IMPORTANT: To implement drop correctly I fear we may have to use a non function 
   version of a store *)


Fixpoint remove_location (st : store) (l : location) : store :=
  match st with
  | nil => nil
  | (hd :: tl)%list => if (eqb l (fst hd)) 
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
  | ((l, (pv, clf)) :: tl)%list => if (eqb clf lf)
      then collect_in_scope tl lf (l :: lst)%list
      else collect_in_scope tl lf lst
  end.

Fixpoint collect_pvs (st : store) (lst : list location) (pvs : list partial_value) 
  : list partial_value :=
  match lst with 
  | nil => pvs
  | (l :: tl)%list => collect_pvs st tl (fst (s_get st l) :: pvs)%list
  end.

Inductive drop : store -> list partial_value -> store -> Prop :=
  | D_nil : forall (st : store),
      drop st nil st
  | D_cons_other : forall (st : store) (pv : partial_value) (tl : list partial_value),
      (forall (l : location), (pv <> # (VOwnRef l))) ->
      drop st (cons pv tl) st
  | D_cons_own : forall (st1 st2 st3 : store)
      (tl : list partial_value) (l l_own : location),
      fst (s_get st1 l_own) = (# (VOwnRef l)) ->
      st2 = remove_location st1 l_own ->
      drop st2 (cons (fst (s_get st1 l)) tl) st3  ->
      drop st1 (cons (# (VOwnRef l)) tl) st2.

Definition drop_ex1_st1 : store :=
    ("lx", (#1,"l")) ::
    ("lp", ((# (VOwnRef "lx")),"m")) ::
    nil.

Definition drop_ex1_st2 : store :=
    ("lx", ((#1),"l")) ::
    nil.

Example drop_ex1 : drop drop_ex1_st1 
  (collect_pvs drop_ex1_st1 ("lp" :: nil)%list nil) 
  drop_ex1_st2.
Proof. simpl. apply D_cons_own with (st3 := drop_ex1_st2) (l_own := "lp").
+ reflexivity.
+ reflexivity.
+ simpl. apply D_cons_other. unfold not. intros l H. injection H as H1. discriminate.
Qed.


Reserved Notation " t '-->' t' '|' l " (at level 40).

Inductive step : lifetime -> (term * store) -> (term * store) -> Prop :=
| R_Copy : forall (w : lval) (v : value) (lf slf : lifetime) (st : store),
    read st w (# v, lf) ->
    (TCopy w, st) --> (TValue v, st) | slf
| R_Move : forall (w : lval) (v : value) (lf slf : lifetime) (st1 st2 : store),
    read st1 w (# v, lf) ->
    write st1 w ## st2 ->
    (TMove w, st1) --> (TValue v, st2) | slf
| R_Box : forall (v : value) (n : location) (slf : lifetime) (st1 st2 : store),
    fst (s_get st1 n) = ## ->
    st2 = cons (n, (# v, "global")) st1 ->
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
    write st2 w (# v2) st3 ->
    (TAssignment w (TValue v2), st1) --> (TValue VUnit, st3) | slf
| R_Declare : forall (v : value) (lx : location) (x : string) (slf : lifetime) (st1 st2 : store),
    st2 = cons (lx, (# v, slf)) st1 ->
    (TDeclaration x (TValue v), st1) --> (TValue VUnit, st2) | slf
| R_Seq : forall (st1 st2 : store) (v : value) (t : term) (slf : lifetime),
    drop st1 (# v :: nil)%list st2 ->
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
    (TSeq t1 t3, st1) --> (TSeq t2 t3, st2) | l_lf
| R_Sub_Asg : forall (st1 st2 : store) (l_lf : lifetime) (t1 t2 : term) (w : lval),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TAssignment w t1, st1) --> (TAssignment w t2, st2) | l_lf
| R_Sub_Decl : forall (st1 st2 : store) (l_lf : lifetime) (t1 t2 : term) (x : string),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TDeclaration x t1, st1) --> (TDeclaration x t2, st2) | l_lf
where " t '-->' t' '|' l " := (step l t t').

Check step.

Inductive multi : Prop -> Prop :=
  | multi_refl : forall (ts : term * store) (lf : lifetime),
      multi (ts --> ts | lf)
  | multi_step : forall (ts1 ts2 ts3 : term * store) (lf : lifetime),
      (ts1 --> ts2 | lf) ->
      multi (ts2 --> ts3 | lf) ->
      multi (ts1 --> ts3 | lf).

Notation " t '-->*' t' | lf" := (multi (t --> t' | lf)) (at level 40).

(* figuring out R_Sub *)

Definition r_sub1_st := ("y", (#1, "l_lf")) :: nil.
Example r_sub1: (THeapAlloc (TCopy (LVar "y")),r_sub1_st) -->
  (THeapAlloc (TValue 1) ,r_sub1_st) | "l_lf".
Proof.
    apply R_Sub_HeapAlloc.
    apply R_Copy with (lf := "l_lf").
      + auto_read.
Qed.

Definition r_sub2_st  := ("y", (#1, "l_lf")) :: nil.
Definition r_sub2_st' := ("y", (#2, "l_lf")) :: nil.
Example r_sub2: 
  (
    (TAssignment (LVar "y") (TValue 2));
    (TAssignment (LVar "x") (TMove (LVar "y")))
  ,r_sub2_st) 
  --> 
  (
    (TValue VUnit);
    (TAssignment (LVar "x") (TMove (LVar "y")))
  ,r_sub2_st') | "l_lf".
Proof.
  apply R_Sub_Seq. apply R_Assign with (st2 := r_sub2_st) (pv1 := (#1, "l_lf")).
  + auto_read.
  + simpl. apply D_cons_other. intros l. intros H. injection H as H1. discriminate.
  + apply Write with (l := "y").
    - simpl. reflexivity.
    - loc_var.
  Qed.

(* worked example 1 *)

Definition we1_1 : (term * store) :=
  (
  <{
    (TDeclaration "x" (TValue 1));
    (TDeclaration "y" (THeapAlloc (TCopy (LVar "x"))));
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  nil
  ).

Definition we1_1_1 : (term * store) :=
  (
  <{
    (TValue VUnit);
    (TDeclaration "y" (THeapAlloc (TCopy (LVar "x"))));
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step1_1 : we1_1 --> we1_1_1 | "l_lf".
Proof.
  apply R_BlockA. apply R_Sub_Seq.
  - apply R_Declare with (lx := "x").
    reflexivity.
Qed.

Definition we1_1_2 : (term * store) :=
  (
  <{
    (TDeclaration "y" (THeapAlloc (TCopy (LVar "x"))));
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step1_2 : we1_1_1 --> we1_1_2 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_Seq.
  apply D_cons_other.
  intros l. intros H.
  discriminate.
Qed.

Definition we1_1_3 : (term * store) :=
  (
  <{
    (TDeclaration "y" (THeapAlloc (TValue 1)));
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step1_3 : we1_1_2 --> we1_1_3 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Sub_Decl.
  apply R_Sub_HeapAlloc.
  apply R_Copy with (lf := "l_lf").
  auto_read.
Qed.

Definition we1_1_4 : (term * store) :=
  (
  <{
    (TDeclaration "y" (TValue (VOwnRef "1")));
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step1_4 : we1_1_3 --> we1_1_4 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Sub_Decl.
  apply R_Box.
  - auto.
  - auto.
Qed.

Definition we1_1_5 : (term * store) :=
  (
  <{
    TValue VUnit;
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("y", (# (VOwnRef "1"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step1_5 : we1_1_4 --> we1_1_5 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Declare with (lx := "y").
  auto.
Qed.

Definition we1_2 : (term * store) :=
  (
  <{
    <{
      (TDeclaration "z" (THeapAlloc (TValue 0)));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("y", (# (VOwnRef "1"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step1_6 : we1_1_5 --> we1_2 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_Seq.
  apply D_cons_other.
  intros l H.
  discriminate.
Qed.

Example we1_step1 : we1_1 -->* we1_2 | "l_lf".
Proof.
  apply multi_step with (ts2 := we1_1_1); try (apply we1_step1_1).
  apply multi_step with (ts2 := we1_1_2); try (apply we1_step1_2).
  apply multi_step with (ts2 := we1_1_3); try (apply we1_step1_3).
  apply multi_step with (ts2 := we1_1_4); try (apply we1_step1_4).
  apply multi_step with (ts2 := we1_1_5); try (apply we1_step1_5).
  apply multi_step with (ts2 := we1_2); try (apply we1_step1_6).
  apply multi_refl.
Qed.

Definition we1_2_1 : (term * store) :=
  (
  <{
    <{
      (TDeclaration "z" (TValue (VOwnRef "2")));
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("2", (#0, "global")) ::
  ("y", (# (VOwnRef "1"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step2_1 : we1_2 --> we1_2_1 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Sub_Decl.
  apply R_Box with (n := "2").
  - auto.
  - auto.
Qed.

Definition we1_2_2 : (term * store) :=
  (
  <{
    <{
      TValue VUnit;
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VOwnRef "1"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step2_2 : we1_2_1 --> we1_2_2 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Declare with (lx := "z"). auto.
Qed.

Definition we1_3 : (term * store) :=
  (
  <{
    <{
      (TAssignment (LVar "y") (TBorrow (LVar "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VOwnRef "1"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step2_3 : we1_2_2 --> we1_3 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Seq.
  apply D_cons_other.
  intros l H; discriminate.
Qed.

Example we1_step2 : we1_2 -->* we1_3 | "l_lf".
Proof.
  apply multi_step with (ts2 := we1_2_1); try (apply we1_step2_1).
  apply multi_step with (ts2 := we1_2_2); try (apply we1_step2_2).
  apply multi_step with (ts2 := we1_3); try (apply we1_step2_3).
  apply multi_refl.
Qed.

Definition we1_3_1 : (term * store) :=
  (
  <{
    <{
      (TAssignment (LVar "y") (TValue (VBorrowRef "z")));
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VOwnRef "1"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step3_1 : we1_3 --> we1_3_1 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Sub_Asg.
  apply R_Borrow.
  loc_var.
Qed.

Definition we1_3_2 : (term * store) :=
  (
  <{
    <{
      TValue VUnit;
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step3_2 : we1_3_1 --> we1_3_2 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Assign with (st2 := 
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("x", (#1, "l_lf"))
  :: nil) (pv1 := (# (VOwnRef "1"), "l_lf")).
  auto_read.
  - simpl. apply D_cons_own with (st3 :=
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ) (l_own := "1").
    + simpl. reflexivity.
    + simpl. reflexivity.
.
  loc_var.
Qed.

Definition we1_4 : (term * store) :=
  (
  <{
    <{
      (TAssignment (LVar "y") (TMove (LVar "z")));
      (TMove (LDeref (LVar "y")));
      (TValue VUnit)
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("1", (#1, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).
