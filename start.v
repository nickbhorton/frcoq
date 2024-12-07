Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.

Open Scope string.
Open Scope list.

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
  | TBox (t : term)
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

Coercion VInt : nat >-> value.
Coercion LVar : string >-> lval.
Coercion TValue : value >-> term.
Notation "'#' v" := (PVDefined v) (at level 0).
Notation "'##'" := (PVUndefined) (at level 0).
Notation "s1 ; s2" := (TSeq s1 s2) (at level 90, right associativity).
Notation "'<{' p '}>' lf" := (TBlock p lf) (at level 91, right associativity).
Notation "'Ɛ'" := (TValue VUnit) (at level 80).


(* state *)
Definition store := list (location * (partial_value * lifetime)).

Notation "lx '|->' '[' pv ']' lf" := ((lx, (pv,lf))) (at level 70).



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
  : option (partial_value * lifetime) :=
  match st with
  | nil => None
  | ((cl, pv_l) :: tl)%list => if (eqb cl l) then Some pv_l else s_get tl l
  end.


Fixpoint s_get_unwrap (st :store) (l : location) 
  : partial_value :=
  match st with
  | nil => ##
  | ((cl, (pv,lf)) :: tl)%list => if (eqb cl l) then pv else s_get_unwrap tl l
  end.


(* These definitions are in support of a equality of lists behavior *)

Fixpoint s_get_all_locations (st : store) (loc_lst : list location)
  : list location :=
  match st with 
  | nil => loc_lst
  | (l,(_,_)) :: tl => s_get_all_locations tl (l :: loc_lst) 
  end.

Definition pvo_eq (pvo1 pvo2 : option (partial_value * lifetime)) : bool :=
  match (pvo1, pvo2) with
  | (None, None) => true
  | (Some (pv1, lf1), Some (pv2, lf2)) => andb (lf1 =? lf2) 
      match (pv1, pv2) with
      | (PVUndefined, PVUndefined) => true
      | (PVDefined v1, PVDefined v2) => 
          match (v1, v2) with
          | (VUnit,VUnit) => true
          | (VInt i1,VInt i2) => (i1 =? i2)%nat
          | (VOwnRef s1, VOwnRef s2) => s1 =? s2
          | (VBorrowRef s1, VBorrowRef s2) => s1 =? s2
          | (_,_) => false
          end
      | (_,_) => false
      end
  | (_,_) => false
  end. 

Fixpoint s_inj (st1 st2 : store) (loc_lst : list location) : bool :=
  match loc_lst with
  | nil => true 
  | hd :: tl => if (pvo_eq (s_get st1 hd) (s_get st2 hd)) then s_inj st1 st2 tl else false
  end.

Definition s_eq (st1 st2 : store) : bool :=
  andb 
  (s_inj st1 st2 (s_get_all_locations st1 nil))
  (s_inj st1 st2 (s_get_all_locations st2 nil)).

Fixpoint s_remove_l (st : store) (l : location) : store :=
  match st with 
  | nil => st
  | (hl, pvl) :: tl => if (l =? hl) then s_remove_l tl l else (hl,pvl) :: (s_remove_l tl l)
  end.

(* 
   store : locations -> (partial_value * lifetimes)
   locations : string
   lifetimes : string
   lf_order : list string
*)


Definition example_store :=
  ("x" |-> [#1]"l_l") ::
  ("p" |-> [# (VBorrowRef "x")]"l_m") ::
  ("d" |-> [# (VBorrowRef "p")]"l_f") ::
  ("t" |-> [# (VBorrowRef "d")]"l_a") ::
  nil.

Definition example_store' :=
  ("x", (#1, "l_l")) ::
  ("p", (# (VBorrowRef "x"), "l_m")) ::
  ("d", (# (VBorrowRef "p"), "l_f")) ::
  ("t", (# (VBorrowRef "d"), "l_a")) :: nil.

Compute s_eq example_store example_store'.

(* SEMANTICS *)

Inductive loc : store -> lval -> location -> Prop :=
  | Loc_Var : forall (st : store) (var_loc : string), 
      (
        exists (pvl : partial_value * lifetime),
        s_get st var_loc = Some pvl
      ) ->
      loc st (LVar var_loc) var_loc
  | Loc_Deref : 
      forall (st : store) (l lw: location) (w : lval) ,
      (
        exists (lf : lifetime), (
        s_get st lw = Some (# (VBorrowRef l), lf) \/
        s_get st lw = Some (# (VOwnRef l), lf))
      ) ->
      loc st w lw ->
      loc st (LDeref w) l.

Ltac loc_var := apply Loc_Var; simpl; eauto.
Ltac loc_deref s := apply Loc_Deref with (lw := s); 
  simpl; try eauto; try (right; reflexivity); try (loc_var).

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

Print example_store.
Compute deref_loc_repeat (example_store) (LDeref "d").


Ltac auto_loc :=
  repeat match goal with
  | [ |- loc ?st (LVar ?x) ?y ] => loc_var
  | [ |- loc ?st (LDeref (LVar ?l)) ?y ] => loc_deref l
  | [ |- loc ?st ?a ?y ] => try loc_deref (find_loc st y)
  end.


Example loc_ex1 : loc example_store "x" "x".
Proof.
  apply Loc_Var. simpl. eauto.
Qed.

Example loc_ex1' : loc example_store "x" "x".
Proof.
  auto_loc.
Qed.

Example loc_ex2 : loc example_store "p" "t".
Proof.
  (* we are stuck because t != p*)
Abort.

Example loc_ex3 : loc example_store "y" "y".
Proof.
  apply Loc_Var. simpl. 
  (* we are stuck because there is no y in example_store *)
Abort.

Example loc_ex4 : loc example_store (LDeref "p") "x".
Proof.
  apply Loc_Deref with (lw := "p"). 
  + simpl. eauto.
  + apply Loc_Var. simpl. eauto.
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
  + simpl. eauto.
  + apply Loc_Deref with (lw := "d").
    - simpl. eauto.
    - apply Loc_Var. simpl. eauto.
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

Inductive read: store -> lval -> partial_value * lifetime -> Prop :=
  | Read : forall (st : store) (w : lval) (pvl : partial_value * lifetime) (l : location), 
      s_get st l = Some pvl ->
      loc st w l ->
      read st w pvl.

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
  + simpl. Abort.
(* we are stuck because reads should not be about to return Undefined values*)


(* 
My first attempt at this in (loc st w l) was instead (loc st' w l) but apparently 
for write to succed the location l has to already be alocated in st.
*)

Inductive write: store -> lval -> partial_value -> store -> Prop :=
  | Write : forall (st st' : store) (pv : partial_value) (l : location) (w : lval),
      s_eq (s_remove_l st l) (s_remove_l st' l) = true ->
      (exists (lf : lifetime ), (s_get st' l = Some (pv, lf))) ->
      loc st w l ->
      write st w pv st'.

Ltac write_rule lv :=
  apply Write with (l := lv); 
    try (simpl; reflexivity);
    try (simpl; eauto);
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
  + simpl. eauto.
  + apply Loc_Var. simpl.  
  Abort.
    (* this fails because x was not defined in st*)

Example write_ex2 :
  write es_1 (LVar "x") (#1) es_1'.
Proof.
  apply Write with (l := "x").
  - simpl. eauto.
  - simpl. eauto.
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
  + simpl. eauto.
  + simpl. eauto.
  + loc_deref "p".
Qed.

Example write_ex3' :
  write (("x", (##, "m")):: nil) (LVar "x") #1 (("x", (#1, "m")) :: nil).
Proof.
  apply Write with (l := "x").
  + simpl. eauto.
  + simpl. eauto.
  + auto_loc.
Qed.

Example write_ex3'' :
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

Fixpoint collect_in_scope (st : store) (lf : lifetime) (lst : list location)
  : list location :=
  match st with 
  | nil => lst
  | ((l, (pv, clf)) :: tl)%list => if (eqb clf lf)
      then collect_in_scope tl lf (l :: lst)%list
      else collect_in_scope tl lf lst
  end.

Fixpoint to_own_refs (lst : list location) (pvs : list partial_value) 
  : list partial_value :=
  match lst with
  | nil => pvs
  | l :: tl => to_own_refs tl (#(VOwnRef l) :: pvs)
  end.

Fixpoint collect_pvs (st : store) (lst : list location) (pvs : list partial_value) 
  : list partial_value :=
  match lst with 
  | nil => pvs
  | (l :: tl)%list =>  
      match s_get st l with
      | Some (pv, lf) => collect_pvs st tl (pv :: pvs)
      | None => collect_pvs st tl pvs
      end
  end.

Inductive drop : store -> list partial_value -> store -> Prop :=
  | D_nil : forall (st : store),
      drop st nil st
  | D_cons_other : forall (st1 st2 : store) (pv : partial_value) (tl : list partial_value),
      drop st1 tl st2 ->
      (forall (l : location), (pv <> # (VOwnRef l))) ->
      drop st1 (cons pv tl) st1
  | D_cons_own : forall (st1 st2 st3: store) (tl : list partial_value) (l : location),
      s_get_unwrap st2 l = ## ->
      drop st2 (s_get_unwrap st1 l :: tl) st3  ->
      drop st1 ((# (VOwnRef l)) :: tl) st3.


Definition drop_ex1_st1 : store :=
    ("lx", (#1,"l")) ::
    ("lp", ((# (VOwnRef "lx")),"m")) ::
    nil.

Definition drop_ex1_st2 : store :=
    ("lx", (##,"global")) ::
    ("lp", (# (VOwnRef "lx"),"m")) ::
    nil.

Example drop_ex1 : drop drop_ex1_st1 
  (# (VOwnRef "lx") :: nil) 
  drop_ex1_st2.
Proof. 
  apply D_cons_own with (st2 := drop_ex1_st2).
  + simpl. reflexivity.
  + apply D_cons_other with (st2 := drop_ex1_st2).
    - apply D_nil.
    - simpl. intros l. intros H. discriminate.
Qed.

Ltac drop_trivial :=
  repeat match goal with
  | [ |- drop ?st (#(VOwnRef ?l) :: ?tl) ?st' ] => try apply D_cons_own with (st2 := st'); simpl;
      try (simpl; reflexivity)
  | [ |- drop ?st (?hd :: ?tl) ?st' ] => try apply D_cons_other with (st2 := st');
      try (simpl; intros l H; discriminate)
  | [ |- drop ?st1 nil ?st2 ] => apply D_nil
  end.

Example drop_ex1' : drop drop_ex1_st1 
  (# (VOwnRef "lx") :: nil) 
  drop_ex1_st2.
Proof. 
  drop_trivial.
Qed.


(* lifetime soundness setupt *)
Definition lf_ordering := list string.
Definition lfo_empty := "global" :: nil. 

Reserved Notation " t '-->' t' '|' l" (at level 40).

Inductive step : lifetime -> (term * store) -> (term * store) -> Prop :=
| R_Copy : forall (w : lval) (v : value) (lf slf : lifetime) (st : store),
    read st w (# v, lf) ->
    (TCopy w, st) --> (TValue v, st) | slf
| R_Move : forall (w : lval) (v : value) (lf slf : lifetime) (st1 st2 : store),
    read st1 w (# v, lf) ->
    write st1 w ## st2 ->
    (TMove w, st1) --> (TValue v, st2) | slf
| R_Box : forall (v : value) (n : location) (slf : lifetime) (st1 st2 : store),
    s_get st1 n = None ->
    ((s_eq st2 (cons (n, (# v, "global")) st1)) = true) ->
    (TBox (TValue v), st1) --> (TValue (VOwnRef n), st2) | slf
| R_Borrow : forall (w : lval) (lw : location) (slf : lifetime) (st : store),
    loc st w lw ->
    (TBorrow w, st) --> (TValue (VBorrowRef lw), st) | slf
| R_MutBorrow : forall (w : lval) (lw : location) (slf : lifetime) (st : store),
    loc st w lw ->
    (TMutBorrow w, st) --> (TValue (VOwnRef lw), st) | slf
| R_Assign : forall (st1 st2 st3 : store) 
    (w : lval) (v2 : value) (slf : lifetime),
    (exists (pv1 : partial_value) (lf : lifetime), 
    read st1 w (pv1, lf) /\ drop st1 (pv1 :: nil) st2) ->
    write st2 w (# v2) st3 ->
    (TAssignment w (TValue v2), st1) --> (Ɛ, st3) | slf
| R_Declare : forall (v : value) 
    (lx : location) (x : string) (slf : lifetime) (st1 st2 : store),
    (s_eq st2 (cons (lx, (# v, slf)) st1) = true) ->
    (TDeclaration x (TValue v), st1) --> (Ɛ, st2) | slf
| R_Seq : forall (st1 st2 : store) (v : value) (t : term) (slf : lifetime),
    drop st1 (# v :: nil) st2 ->
    (TSeq (TValue v) t, st1) --> (t, st2) | slf
| R_BlockA : forall (st1 st2 : store) (l_lf m_lf : lifetime) (t1 t2 : term),
    (t1, st1) --> (t2, st2) | m_lf ->
    (TBlock t1 m_lf, st1) --> (TBlock t2 m_lf, st2) | l_lf
| R_BlockB : forall (st1 st2 : store) (l_lf m_lf : lifetime) (v : value),
    drop st1 (to_own_refs (collect_in_scope st1 m_lf nil) nil) st2 ->
    (TBlock (TValue v) m_lf, st1) --> (TValue v, st2) | l_lf
| R_Sub_Box : forall (st1 st2 : store) (l_lf : lifetime) (t1 t2 : term),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TBox t1, st1) --> (TBox t2, st2) | l_lf
| R_Sub_Seq : forall (st1 st2 : store) (l_lf : lifetime) (t1 t2 t3 : term),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TSeq t1 t3, st1) --> (TSeq t2 t3, st2) | l_lf
| R_Sub_Asg : forall (st1 st2 : store) 
    (l_lf : lifetime) (t1 t2 : term) (w : lval),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TAssignment w t1, st1) --> (TAssignment w t2, st2) | l_lf
| R_Sub_Decl : forall (st1 st2 : store) 
    (l_lf : lifetime) (t1 t2 : term) (x : string),
    (t1,st1) --> (t2,st2) | l_lf ->
    (TDeclaration x t1, st1) --> (TDeclaration x t2, st2) | l_lf
where " t '-->' t' '|' l" := (step l t t').

Check step.

Inductive multi : Prop -> Prop :=
  | multi_refl : forall (ts : term * store) (lf : lifetime) ,
      multi (ts --> ts | lf)
  | multi_step : forall (ts1 ts2 ts3 : term * store) (lf : lifetime),
      (ts1 --> ts2 | lf) ->
      multi (ts2 --> ts3 | lf) ->
      multi (ts1 --> ts3 | lf).

Notation " t '-->*' t' '|' lf" := (multi (t --> t' | lf)) (at level 40).

(* figuring out R_Sub *)

Definition r_sub1_st := ("y", (#1, "l_lf")) :: nil.
Example r_sub1: (TBox (TCopy (LVar "y")),r_sub1_st) -->
  (TBox (TValue 1) ,r_sub1_st) | "l_lf".
Proof.
    apply R_Sub_Box.
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
    (Ɛ);
    (TAssignment (LVar "x") (TMove (LVar "y")))
  ,r_sub2_st') | "l_lf".
Proof.
  apply R_Sub_Seq. apply R_Assign with (st2 := r_sub2_st).
  + exists #1. exists "l_lf". split.
    - auto_read.
    - drop_trivial.
  + auto_write.
  Qed.

(* worked example 1 *)

Definition we1_1 : (term * store) :=
  (
  <{
    TDeclaration "x" 1;
    TDeclaration "y" (TBox (TCopy "x"));
    <{
      TDeclaration "z" (TBox 0);
      TAssignment "y" (TBorrow "z");
      TAssignment "y" (TMove "z");
      TMove (LDeref "y");
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  nil
  ).

Definition we1_1_1 : (term * store) :=
  (
  <{
    Ɛ;
    TDeclaration "y" (TBox (TCopy (LVar "x")));
    <{
      TDeclaration "z" (TBox (TValue 0));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
    TDeclaration "y" (TBox (TCopy (LVar "x")));
    <{
      TDeclaration "z" (TBox (TValue 0));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("x", (#1, "l_lf"))
  :: nil
  ).

Lemma sequence_unit: forall (st : store) (t : term) (lf : lifetime), 
  (Ɛ;
  t, st)
  -->
  (t, st) | lf.
Proof.
  intros st t lf.
  apply R_Seq. drop_trivial.
Qed.

Example we1_step1_2 : we1_1_1 --> we1_1_2 | "l_lf".
Proof.
  apply R_BlockA.
  apply sequence_unit. 
Qed.

Definition we1_1_3 : (term * store) :=
  (
  <{
    TDeclaration "y" (TBox (TValue 1));
    <{
      TDeclaration "z" (TBox (TValue 0));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
  apply R_Sub_Box.
  apply R_Copy with (lf := "l_lf").
  auto_read.
Qed.

Definition we1_1_4 : (term * store) :=
  (
  <{
    TDeclaration "y" (TValue (VOwnRef "1"));
    <{
      TDeclaration "z" (TBox (TValue 0));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
    Ɛ;
    <{
      TDeclaration "z" (TBox (TValue 0));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
      TDeclaration "z" (TBox (TValue 0));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
  apply sequence_unit.
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
      TDeclaration "z" (TValue (VOwnRef "2"));
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
      Ɛ;
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
      TAssignment (LVar "y") (TBorrow (LVar "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
  apply sequence_unit.
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
      TAssignment (LVar "y") (TValue (VBorrowRef "z"));
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
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
      Ɛ;
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("1", (##, "global")) ::
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
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).
  - exists (# (VOwnRef "1")). exists "l_lf". split.
    + auto_read.
    + apply D_cons_own with (st2 := 
        ("z", (# (VOwnRef "2"), "m_lf")) ::
        ("2", (#0, "global")) ::
        ("y", (# (VBorrowRef "z"), "l_lf")) ::
        ("1", (##, "global")) ::
        ("x", (#1, "l_lf"))
        :: nil).
        * simpl. reflexivity.
        * simpl. apply D_cons_other with (st2 := 
        ("z", (# (VOwnRef "2"), "m_lf")) ::
        ("2", (#0, "global")) ::
        ("y", (# (VBorrowRef "z"), "l_lf")) ::
        ("1", (##, "global")) ::
        ("x", (#1, "l_lf"))
        :: nil).
        { apply D_nil. }
        { intros l H. discriminate. }
  - auto_write.
Qed.


Definition we1_4 : (term * store) :=
  (
  <{
    <{
      TAssignment (LVar "y") (TMove (LVar "z"));
      TMove (LDeref (LVar "y"));
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (# (VOwnRef "2"), "m_lf")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step3_3 : we1_3_2 --> we1_4 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply sequence_unit.
Qed.

(* correct here *)

Definition we1_4_1 : (term * store) :=
  (
  <{
    <{
      TAssignment (LVar "y") (TValue (VOwnRef "2"));
      TMove (LDeref (LVar "y"));
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (##, "global")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step4_1 : we1_4 --> we1_4_1 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Sub_Asg.
  apply R_Move with (lf := "m_lf").
  - auto_read.
  - auto_write.
Qed.

Definition we1_4_2 : (term * store) :=
  (
  <{
    <{
      Ɛ;
      TMove (LDeref "y");
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (##, "global")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VOwnRef "2"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we1_step4_2 : we1_4_1 --> we1_4_2 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Assign with (st2 :=
  ("z", (##, "global")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VBorrowRef "z"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).
  - exists (# (VBorrowRef "z")). exists "l_lf". split.
    + auto_read.
    + drop_trivial.
  - auto_write.
Qed.

Definition we1_5 : (term * store) :=
  (
  <{
    <{
      TMove (LDeref (LVar "y"));
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (##, "global")) ::
  ("2", (#0, "global")) ::
  ("y", (# (VOwnRef "2"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we_step5 : we1_4_2 --> we1_5 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply sequence_unit.
Qed.

Definition we1_6 : (term * store) :=
  (
  <{
    <{
      TValue 0;
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (##, "global")) ::
  ("2", (##, "global")) ::
  ("y", (# (VOwnRef "2"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we_step6 : we1_5 --> we1_6 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Sub_Seq.
  apply R_Move with (lf := "global").
  - auto_read.
  - auto_write.
Qed.

Definition we1_7 : (term * store) :=
  (
  <{
    <{
      Ɛ
    }> "m_lf"
  }> "l_lf"
  ,
  ("z", (##, "global")) ::
  ("2", (##, "global")) ::
  ("y", (# (VOwnRef "2"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we_step7 : we1_6 --> we1_7 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockA.
  apply R_Seq.
  drop_trivial.
Qed.

Definition we1_8 : (term * store) :=
  (
  <{
      Ɛ
  }> "l_lf"
  ,
  ("z", (##, "global")) ::
  ("2", (##, "global")) ::
  ("y", (# (VOwnRef "2"), "l_lf")) ::
  ("1", (##, "global")) ::
  ("x", (#1, "l_lf"))
  :: nil
  ).

Example we_step8 : we1_7 --> we1_8 | "l_lf".
Proof.
  apply R_BlockA.
  apply R_BlockB.
  simpl. drop_trivial.
Qed.

Definition we1_9 : (term * store) :=
  (
      Ɛ
  ,
  ("z", (##, "global")) ::
  ("2", (##, "global")) ::
  ("y", (##, "global")) ::
  ("1", (##, "global")) ::
  ("x", (##, "global"))
  :: nil
  ).

Example we_step9 : we1_8 --> we1_9 | "l_lf".
Proof.
  apply R_BlockB.
  simpl. 
  drop_trivial.
Qed.
