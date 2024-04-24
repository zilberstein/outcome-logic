Require Import partial.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
Require Import  Coq.Logic.JMeq.
From Coq Require Import Logic.PropExtensionality.

Record exec_model_consts : Type := make_exec_model_consts
  {
    M : Type -> Type;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
    unit : forall {A : Type}, A -> M A ;
    exec_partial : forall (A : Type), relation (M A);
    bop : forall (A: Type), partial_fun (exec_partial A) (M A);
    id : forall (A: Type), M A;
  }.

Record exec_model_theory (E : exec_model_consts) : Prop := make_emt
{
  (* PCM *)
  pcm_comm : forall (A : Type) (x y : (M E) A) (Hxy : exec_partial E A x y), 
    exists Hyx, ap (bop E A) x y Hxy = ap (bop E A) y x Hyx ;
  pcm_assoc : forall (A : Type) (x y z : (M E) A) (Hyz : exec_partial E A y z) 
  (Hx_yz : exec_partial E A x (ap (bop E A) y z Hyz)),
    exists Hxy Hxy_z,
    ap (bop E A) x (ap (bop E A) y z Hyz) Hx_yz = 
    ap (bop E A) (ap (bop E A) x y Hxy) z Hxy_z ; 
  pcm_id : forall (A : Type) (x : (M E) A), 
    exists (Hx : exec_partial E A x (id E A)),
    ap (bop E A) x (id E A) Hx = x;

  (* Preservation of monad bind*)
  preserve_bind1 : forall (A B: Type) (f : A -> (M E) B) (x y : (M E) A) 
  (Hxy : exec_partial E A x y),
    exists H,
    bind E (ap (bop E A) x y Hxy) f = ap (bop E B) (bind E x f) (bind E y f) H;
  preserve_bind2 : forall (A B : Type) (f : A -> (M E) B),
    bind E (id E A) f = id E B ;

  (* Need to find a good way to formalize this rule to require that 
     f + g is defined *)
  preserve_bind3 : forall (A B : Type) (f g : A -> (M E) B) (x : (M E) A)
    (Hfg : forall (y : A), exec_partial E B (f y) (g y)),
    exists H,
    ap (bop E B) (bind E x f) (bind E x g) H = 
    bind E x (fun y => ap (bop E B) (f y) (g y) (Hfg y));
  
  (* Monad Laws *)
  bind_with_unit : forall (A : Type) (m : (M E) A),
    bind E m (unit E) = m ;
  bind_of_unit : forall (A B : Type) (f : A -> (M E) B) (x : A),
    bind E (unit E x) f = f x ;
  bind_composition : forall (A B C : Type) (f : A -> (M E) B) 
  (g : B -> (M E) C) (m : (M E) A),
    bind E (bind E m f) g = bind E m (fun x => bind E (f x) g)
}.

(* Some potentially useful Theorems *)

Theorem bop_id_defined : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex) (A : Type) (x y : M Ex A),
  x = id Ex A \/ y = id Ex A -> exec_partial Ex A x y.
Proof.
  intros. assert (forall s, exists pf, ap (bop Ex A) s (id Ex A) pf = s).
    { apply (pcm_id Ex Ext). }
  assert (forall s, exec_partial Ex A s (id Ex A)). { apply H0. }
  assert (forall s, exists pf', ap (bop Ex A) s (id Ex A) (H1 s) = ap (bop Ex A) (id Ex A) s pf').
    { intros. apply (pcm_comm Ex Ext). }
  assert (exec_partial Ex A (id Ex A) y). { apply H2. }
  destruct H.
  - subst. easy.
  - subst. easy.
Qed.

Theorem pcm_id_comm : forall (E : exec_model_consts) (Ext: exec_model_theory E) 
  (A : Type) (x : (M E) A), 
  exists (Hx : exec_partial E A (id E A) x), ap (bop E A) (id E A) x Hx = x.
Proof.
  intros. assert (forall Hx, exists H', ap (bop E A) x (id E A) Hx = ap (bop E A) (id E A) x H').
    { intros. apply (pcm_comm E Ext). }
  assert (exists Hx, ap (bop E A) x (id E A) Hx = x ).
    { apply (pcm_id E Ext). }
  inversion H0. specialize (H x0). inversion H. exists x1. rewrite <- H2. apply H1.
Qed.

(* Before defining the syntax and semantics of the command language, we define
   program states and semantics for a language of atomic commands on those 
   states as described in Example 3.4 of the Completeness paper *)

(* Arithmetic Expressions *)
Inductive aexp : Type :=  
  | num (n : nat)
  | avar (x : string)
  | plus (n1 n2 : aexp)
  | minus (n1 n2 : aexp)
  | mult (n1 n2 : aexp).

(* Boolean Expressions *)
Inductive bexp : Type := 
  | BTrue
  | BFalse
  | Bvar (x : string)
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNeg (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp).

Inductive val : Type :=
  | Aval (n : nat)
  | Bval (b : bool).

Definition state := string -> val.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with 
  | num n => n
  | avar x => match (st x) with
              | Aval n => n
              | Bval false => 0 (*Placeholder*)
              | Bval true => 1
              end
  | plus a1 a2 => (aeval st a1) + (aeval st a2)
  | minus a1 a2 => (aeval st a1) - (aeval st a2)
  | mult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | Bvar x => match (st x) with
              | Aval 0 => false (*Placeholder*)
              | Aval _ => true
              | Bval b => b
              end
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BNeq a1 a2 => negb ((aeval st a1) =? (aeval st a2))
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BGt a1 a2 => negb ((aeval st a1) <=? (aeval st a2))
  | BNeg b => negb (beval st b)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  | BOr b1 b2 => orb (beval st b1) (beval st b2)
  end.

Inductive vexp : Type :=
  | Value (v : val)
  | Var (x : string)
  | Vaexp (a : aexp)
  | Vbexp (b : bexp).

Definition veval (st : state) (v : vexp) : val :=
  match v with
  | Value v => v
  | Var x => st x
  | Vaexp a => Aval (aeval st a)
  | Vbexp b => Bval (beval st b)
  end.

(* Syntax and Semantics for atomic commands *)
Inductive CAtomic (Ex : exec_model_consts): Type :=
 | CAssume (e : vexp)
 | CAsgn (x : string) (v : vexp).

Definition ceval_atomic (Ex : exec_model_consts) (st : state) (c : CAtomic Ex) : (M Ex state) :=
  match c with
  | CAssume _ e => match veval st e with
                  | Bval false => id Ex state
                  | _ => unit Ex st
                  end
  | CAsgn _ x v => let st' := fun x' => if String.eqb x x' then (veval st v) else (st x') in
                  unit Ex st'
                 end.
          

Definition compatible (e1 e2 : vexp) : Prop :=
  forall st : state,
  (veval st e1 = Bval false) \/ (veval st e2 = Bval false).


Definition is_total (Ex : exec_model_consts) : Prop :=
  forall (A : Type) (x y : M Ex A),
  exec_partial Ex A x y.
  
(* The below is a failed attempt at ceval where we tried to define it by inducting
    on a proof of well-formed-ness of commands, but this ended up being too 
    complicated when trying to do proofs involving ceval as it made it harder 
    to simpl things. *)

(* Inductive wf_com (Ex : exec_model_consts) :  com -> Type :=
  | wf_div : wf_com Ex CDiv
  | wf_skip : wf_com Ex CSkip
  | wf_seq : forall (c1 c2 : com), 
    wf_com Ex c1 -> wf_com Ex c2 -> wf_com Ex (CSeq c1 c2)
  | wf_plus_total : forall (c1 c2 : com), 
      is_total Ex -> wf_com Ex c1 -> wf_com Ex c2 -> wf_com Ex (CPlus c1 c2)
  | wf_plus : forall (e1 e2 : vexp) (c1 c2 : com), 
      compatible e1 e2 -> wf_com Ex c1 -> 
      wf_com Ex c2 -> 
      wf_com Ex (CPlus (CSeq (CAtom (CAssume e1)) c1) (CSeq (CAtom (CAssume e2)) c2))
  | wf_atom : forall (c : CAtomic), wf_com Ex (CAtom c).


Program Fixpoint ceval (Ex : exec_model_consts) (Ext : exec_model_theory Ex) 
  (c : com) (st : state) (wfc : wf_com Ex c) {struct wfc} : (M Ex state) :=
  match wfc with
  | wf_div _ => id Ex state
  | wf_skip _ => unit Ex st
  | wf_seq _ c1 c2 wf1 wf2 => 
      bind Ex (ceval Ex Ext c1 st wf1) (fun st' => ceval Ex Ext c2 st' wf2)
  | wf_atom _ ca => ceval_atomic Ex st ca
  | wf_plus_total _ c1 c2 compat wf1 wf2 => 
      ap (bop Ex state) (ceval Ex Ext c1 st wf1) (ceval Ex Ext c2 st wf2) _ 
  | wf_plus _ e1 e2 c1 c2 compat wf1 wf2 => 
    match veval st e1 with
    | Bval false => (ceval Ex Ext c2 st wf2) 
    | _ => (ceval Ex Ext c1 st wf1)
    end
  end. *)

(* Below, we try to define the denotational semantics w/o needing a proof of 
   well-formed-ness of commands *)

(* Note that the CPlus (non-total case) definition is implicitly
    (Assume e1 ; c1) + (Assume e2 ; c2 ) *)
Inductive com (Ex : exec_model_consts) : Type :=
  | CDiv
  | CSkip 
  | CSeq (c1 c2 : com Ex)
  | CPlus_total (c1 c2 : com Ex) (pf : is_total Ex)
  | CPlus (e1 e2 : vexp) (c1 c2 : com Ex) (pf : compatible e1 e2)
  | CAtom (c : CAtomic Ex).

Program Fixpoint ceval (Ex : exec_model_consts) (Ext : exec_model_theory Ex) 
  (c : com Ex) (st : state) : (M Ex state) :=
  match c with
  | CDiv _ => id Ex state
  | CSkip _ => unit Ex st
  | CSeq _ c1 c2 => 
      bind Ex (ceval Ex Ext c1 st) (fun st' => ceval Ex Ext c2 st')
  | CAtom _ ca => ceval_atomic Ex st ca
  | CPlus_total _ c1 c2 pf => 
      ap (bop Ex state) (ceval Ex Ext c1 st) (ceval Ex Ext c2 st) _ 
  | CPlus _ e1 e2 c1 c2 pf => 
    match veval st e1 with
    (* | Bval false => (ceval Ex Ext c2 st)  *)
    | Bval false => match veval st e2 with
                    | Bval false => id Ex state
                    | _ => ceval Ex Ext c2 st
                    end
    | _ => (ceval Ex Ext c1 st)
    end
  end.

(* Notations for arithmetic and boolean expressions
   (These are adapted from the Imp chapter of PLF) *)
   Coercion avar : string >-> aexp.
   Coercion Var : string >-> vexp.
   Coercion num : nat >-> aexp.
   
   Declare Custom Entry com.
   Declare Scope com_scope.
   
   Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
   Notation "( x )" := x (in custom com, x at level 99) : com_scope.
   Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
   Notation "f x .. y" := (.. (f x) .. y)
                     (in custom com at level 0, only parsing,
                     f constr at level 0, x constr at level 9,
                     y constr at level 9) : com_scope.
   Notation "x + y"   := (plus x y) (in custom com at level 50, left associativity).
   Notation "x - y"   := (minus x y) (in custom com at level 50, left associativity).
   Notation "x * y"   := (mult x y) (in custom com at level 40, left associativity).
   Notation "'true'"  := true (at level 1).
   Notation "'true'"  := BTrue (in custom com at level 0).
   Notation "'false'" := false (at level 1).
   Notation "'false'" := BFalse (in custom com at level 0).
   Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
   Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
   Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
   Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
   Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
   Notation "'~' b"   := (BNeg b) (in custom com at level 75, right associativity).
   
   (* Now, we define some notations for commands *)
   Coercion CAtom : CAtomic >-> com.
   
   Notation " [ 'div' e ]"  :=
            (CDiv e) (in custom com at level 0) : com_scope.
   Notation "[ 'skip' e ]"  :=
            (CSkip e) (in custom com at level 0) : com_scope.
   Notation "[ 'assume' Ex ] e "  :=
             (CAssume Ex e) (in custom com at level 0) : com_scope.
   Notation "x [:= e ] y "  :=
            (CAsgn e x y)
               (in custom com at level 0, x constr at level 0,
                y at level 85, no associativity) : com_scope.
   Notation "x [; e ] y " :=
            (CSeq e x y)
              (in custom com at level 90, right associativity) : com_scope.
   Notation "pf -> x [+ e ] y " := 
            (CPlus_total e x y pf) 
              (in custom com at level 50, left associativity).
   Notation "[ e1 c1 ] [+ e ] [ e2 c2 ]" := 
            (CPlus e e1 e2 c1 c2) 
              (in custom com at level 50, left associativity).

Open Scope com_scope.

(* We can then prove that the definition of ceval above is equivalent to the
   definition using the execution models binary operation *)

Lemma guard_false_implies_id : forall (Ex : exec_model_consts) 
  (Ext : exec_model_theory Ex) (st : state) (e : vexp) (c : com Ex),
  veval st e = Bval false ->
  ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e)) c) st = id Ex state.
Proof.
  intros. simpl. rewrite H. apply (preserve_bind2 Ex Ext).
Qed.

Theorem compatible_ceval_plus : forall (Ex : exec_model_consts)
  (Ext : exec_model_theory Ex) (st : state) (e1 e2 : vexp) (c1 c2 : com Ex)
  (compat : compatible e1 e2),
  exists H,
  ceval Ex Ext (CPlus Ex e1 e2 c1 c2 compat) st = 
  ap (bop Ex state) (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st)
  (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st) H.
Proof.
  intros. unfold compatible in compat.
  assert (veval st e1 = Bval false \/ veval st e2 = Bval false).
    { apply compat. }
  destruct H.
  - assert (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st = id Ex state).
      { apply guard_false_implies_id. apply H. }
    rewrite H0. 
    assert (exists (Hid : exec_partial Ex state (id Ex state)
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st)),
      ap (bop Ex state) (id Ex state) 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st) Hid = 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st)).
      { apply (pcm_id_comm Ex Ext). }
    inversion H1. exists x. rewrite H2. simpl. rewrite H. destruct (veval st e2).
    + rewrite (bind_of_unit Ex Ext). reflexivity.
    + destruct b.
      * rewrite (bind_of_unit Ex Ext). reflexivity.
      * rewrite (preserve_bind2 Ex Ext). reflexivity.
  - assert (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st = id Ex state).
      { simpl. rewrite H. apply (preserve_bind2 Ex Ext). }
    rewrite H0. 
    assert (exists (Hid : exec_partial Ex state 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st) (id Ex state)),
      ap (bop Ex state) 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st) (id Ex state) Hid = 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st)).
      { apply (pcm_id Ex Ext). }
    inversion H1. exists x. rewrite H2. simpl. rewrite H. destruct (veval st e1).
    + rewrite (bind_of_unit Ex Ext). reflexivity.
    + destruct b.
      * rewrite (bind_of_unit Ex Ext). reflexivity.
      * rewrite (preserve_bind2 Ex Ext). reflexivity.
Qed.


Theorem partial_proof_irrelevance : forall (Ex : exec_model_consts) (A : Type)
  (x y : M Ex A) (pf1 pf2 : exec_partial Ex A x y),
  ap (bop Ex A) x y pf1 = ap (bop Ex A) x y pf2.
Proof.
  intros. assert (pf1 = pf2).
    { apply proof_irrelevance. }
  rewrite H. reflexivity. 
Qed.


Theorem compatible_ceval_plus_rev : forall (Ex : exec_model_consts)
  (Ext : exec_model_theory Ex) (st : state) (e1 e2 : vexp) (c1 c2 : com Ex)
  (compat : compatible e1 e2) {H},
  ap (bop Ex state) (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st)
  (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st) H =
  ceval Ex Ext (CPlus Ex e1 e2 c1 c2 compat) st.
Proof.
  intros. generalize dependent H. 
  assert (exists H,
    ceval Ex Ext (CPlus Ex e1 e2 c1 c2 compat) st = 
    ap (bop Ex state) (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st)
    (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st) H).
    { apply compatible_ceval_plus. }
  inversion H.
  rewrite H0. intros. apply partial_proof_irrelevance.
Qed.