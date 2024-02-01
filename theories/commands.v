Require Import partial.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
Require Import  Coq.Logic.JMeq.

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
    exists Hbind,
    bind E (ap (bop E A) x y Hxy) f = ap (bop E B) (bind E x f) (bind E y f) Hbind;
  preserve_bind2 : forall (A B : Type) (f : A -> (M E) B) (x : (M E) A),
    bind E (id E A) f = id E B ;
  
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
Inductive CAtomic : Type :=
 | CAssume (e : vexp)
 | CAsgn (x : string) (v : vexp).

Definition ceval_atomic (Ex : exec_model_consts) (st : state) (c : CAtomic) : (M Ex state) :=
  match c with
  | CAssume e => match veval st e with
                  | Bval true => unit Ex st
                  | _ => id Ex state
                  end
  | CAsgn x v => let st' := fun x' => if String.eqb x x' then (veval st v) else (st x') in
                  unit Ex st'
                 end.

(* Defining the command language *)
Inductive com : Type :=
  | CDiv
  | CSkip 
  | CSeq (c1 c2 : com)
  | CPlus (c1 c2 : com)
  | CAtom (c : CAtomic).


Definition compatible (Ex : exec_model_consts) (e1 e2 : vexp) : Prop :=
  forall st : state, exists He x, 
  ap (bop Ex val) (unit Ex (veval st e1)) (unit Ex (veval st e2)) He = x.


Definition compatible' (e1 e2 : vexp) : Prop :=
  forall st : state,
  (veval st e1 = Bval false) \/ (veval st e2 = Bval false).


Definition is_total (Ex : exec_model_consts) : Prop :=
  forall (A : Type) (x y : M Ex A),
  exec_partial Ex A x y.
  

Inductive wf_com (Ex : exec_model_consts) :  com -> Type :=
  | wf_div : wf_com Ex CDiv
  | wf_skip : wf_com Ex CSkip
  | wf_seq : forall (c1 c2 : com), 
    wf_com Ex c1 -> wf_com Ex c2 -> wf_com Ex (CSeq c1 c2)
  | wf_plus_total : forall (c1 c2 : com), 
      is_total Ex -> wf_com Ex c1 -> wf_com Ex c2 -> wf_com Ex (CPlus c1 c2)
  | wf_plus : forall (e1 e2 : vexp) (c1 c2 : com), 
      compatible' e1 e2 -> wf_com Ex c1 -> 
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
  end.


(*IN PROGRESS*)
(* Theorem compatible_ceval_plus : forall (Ex : exec_model_consts) 
  (Ext : exec_model_theory Ex) (st : state) (e1 e2 : vexp) (c1 c2 : com) 
  (compat_pf : compatible' e1 e2)  (wf1 : wf_com Ex c1) 
  (wf2 : wf_com Ex c2) (wfc : wf_com Ex 
  (CPlus (CSeq (CAtom (CAssume e1)) c1) (CSeq (CAtom (CAssume e2)) c2))), 
  exists wf1' wf2' Hceval,
  (ceval Ex Ext 
  (CPlus (CSeq (CAtom (CAssume e1)) c1) (CSeq (CAtom (CAssume e2)) c2)) st wfc)
  = ap (bop Ex state) (ceval Ex Ext (CSeq (CAtom (CAssume e1)) c1) st wf1')
    (ceval Ex Ext (CSeq (CAtom (CAssume e2)) c2) st wf2') Hceval.
Proof.
  intros.
  remember (wf_atom Ex (CAssume e1)) as wf_assume1.
  remember (wf_seq Ex (CAtom (CAssume e1)) c1 wf_assume1 wf1) as wf_seq1.

  remember (wf_atom Ex (CAssume e2)) as wf_assume2.
  remember (wf_seq Ex (CAtom (CAssume e2)) c2 wf_assume2 wf2) as wf_seq2.

  exists wf_seq1. exists wf_seq2.

  assert (exec_partial Ex state (ceval Ex Ext (CSeq (CAtom (CAssume e1)) c1) st wf_seq1)
  (ceval Ex Ext (CSeq (CAtom (CAssume e2)) c2) st wf_seq2)).
  { 
    apply bop_id_defined. easy. unfold compatible' in compat_pf. 
    assert (veval st e1 = Bval false \/ veval st e2 = Bval false).
   { apply compat_pf. } destruct H.
    - left. rewrite Heqwf_seq1. rewrite Heqwf_assume1. 
      simpl. rewrite H. apply (preserve_bind2 Ex Ext). 
      remember (ceval Ex Ext (CSeq (CAtom (CAssume e1)) c1) st wf_seq1) as res.
      apply res.
    - right. rewrite Heqwf_seq2. rewrite Heqwf_assume2. 
    simpl. rewrite H. apply (preserve_bind2 Ex Ext). 
    remember (ceval Ex Ext (CSeq (CAtom (CAssume e2)) c2) st wf_seq2) as res.
    apply res.
  }
  exists H.

  unfold compatible' in compat_pf. assert (veval st e1 = Bval false \/ veval st e2 = Bval false).
   { apply compat_pf. }
  destruct H0.
  - assert (ceval Ex Ext (CSeq (CAtom (CAssume e1)) c1) st wf_seq1 = id Ex state).
    { rewrite Heqwf_seq1. rewrite Heqwf_assume1. simpl. rewrite H0. 
      apply (preserve_bind2 Ex Ext).  
      remember (ceval Ex Ext (CSeq (CAtom (CAssume e1)) c1) st wf_seq1) as res.
      apply res. } destruct wfc.
      + simpl.
    replace (ceval Ex Ext (CSeq (CAtom (CAssume e1)) c1) st wf_seq1) with 
    (id Ex state). *)
    