Require Import commands.
Require Import partial.

Definition assertion (Ex : exec_model_consts) := M Ex state -> Prop.

(* Reorder the arguments of ceval to use in bind *)
Definition ceval' (Ex : exec_model_consts) (Ext : exec_model_theory Ex) 
  (c : com) (wfc : wf_com Ex c) (st : state) :=
  ceval Ex Ext c st wfc. 

(* Define the monadic lifting of denotational semantics (ceval) *)
Definition ceval_lifted (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (c : com) (st : M Ex state) (wfc : wf_com Ex c) :=
  bind Ex st (ceval' Ex Ext c wfc).

Definition outcome_triple (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (phi : assertion Ex) (c : com) (wfc : wf_com Ex c) (psi : assertion Ex) := 
  forall (m : M Ex state),
  phi m -> psi (ceval_lifted Ex Ext c m wfc).

(* Notations *)
Declare Scope OL_scope.
Open Scope OL_scope.

Notation "< phi > c wfc Ex Ext < psi >" :=
  (outcome_triple Ex Ext phi c wfc psi) (at level 90, psi at next level)
  : OL_scope.

(* Next, we define the different BI assertions that an outcome assertion can be *)
Definition Top (Ex : exec_model_consts) : assertion Ex := 
  fun (m : M Ex state) => True.

Definition Bot (Ex : exec_model_consts) : assertion Ex := 
  fun (m : M Ex state) => False.

Definition T_plus (Ex : exec_model_consts) : assertion Ex :=
  fun (m : M Ex state) => m = id Ex state.

Definition AndOC (Ex : exec_model_consts)  (P Q : assertion Ex) : assertion Ex :=
  fun (m : M Ex state) => P m /\ Q m.

Definition OPlus (Ex : exec_model_consts) (P Q : assertion Ex) : assertion Ex := 
  fun (m : M Ex state) => exists (m1 m2 : M Ex state) H, 
  ap (bop Ex state) m1 m2 H = m /\ P m1 /\ P m2.

Definition ImpliesOC (Ex : exec_model_consts) (P Q : assertion Ex) : assertion Ex :=
  fun (m : M Ex state) => forall (m': M Ex state), m = m' -> P m' -> Q m'.

Definition AtomicAssn (Ex : exec_model_consts) (P : M Ex state -> Prop) : assertion Ex :=
  fun (m : M Ex state) => P m.

(* Defining inference rules *)
Inductive rule (Ex : exec_model_consts) (Ext : exec_model_theory Ex) :
  (assertion Ex) -> com -> (assertion Ex) -> Prop :=
  (* | zero_rule : forall (P : assertion Ex), rule Ex Ext P CDiv (T_plus Ex) *)
  | one_rule : forall (P : assertion Ex), rule Ex Ext P CSkip P
  | seq_rule : forall (P Q R : assertion Ex) (c1 c2 : com),
                rule Ex Ext P c1 Q -> rule Ex Ext Q c2 R ->
                rule Ex Ext P (CSeq c1 c2) R
  | split_rule : forall (P1 Q1 P2 Q2 : assertion Ex) (c : com),
                  rule Ex Ext P1 c Q1 -> rule Ex Ext P2 c Q2 ->
                  rule Ex Ext (OPlus Ex P1 P2) c (OPlus Ex Q1 Q2)
  | empty_rule : forall (c : com), rule Ex Ext (T_plus Ex) c (T_plus Ex)
  | true_rule : forall (P : assertion Ex) (c : com), 
                  rule Ex Ext P c (Top Ex)
  | false_rule : forall (P : assertion Ex) (c : com),
                  rule Ex Ext (Bot Ex) c P
  | consequence_rule : forall (P' P Q Q' : assertion Ex) (c : com),
                    forall (m : M Ex state), ImpliesOC Ex P' P m ->
                    rule Ex Ext P c Q ->
                    forall (m : M Ex state), ImpliesOC Ex Q Q' m ->
                    rule Ex Ext P' c Q'
  | plus_rule : forall (P Q1 Q2 : assertion Ex) (c1 c2 : com),
                  rule Ex Ext P c1 Q1 -> rule Ex Ext P c2 Q2 ->
                  rule Ex Ext P (CPlus c1 c2) (OPlus Ex Q1 Q2).


(*---------------- Soundness of Inference Rules ----------------*)
(* We now begin proving the soundness of Outcome Logic. To begin,
   we show that the conclusion of every inference rule is a valid
   outcome triple given the premises and vice versa. *)

   (*
   <P>*)

Lemma wf_seq_eq : forall (Ex : exec_model_consts)  (c1 c2 : com)
  (wfc : wf_com Ex (CSeq c1 c2)), 
  exists (wfc1 : wf_com Ex c1) (wfc2 : wf_com Ex c2),
    wfc = wf_seq Ex c1 c2 wfc1 wfc2.
Proof.
  intros. eexists. eexists.
  Admitted.


Theorem OL_sound : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (P Q : assertion Ex) (c : com) (wfc : wf_com Ex c),
  rule Ex Ext P c Q -> outcome_triple Ex Ext P c wfc Q.
Proof.
  (* intros. induction H.
  - admit.
  - unfold outcome_triple ; intros. unfold ceval_lifted ; unfold ceval'.
    destruct wfc ; simpl. 
    + simpl. 
    unfold outcome_triple.
  - intros. unfold ceval_lifted ; unfold ceval'. destruct wfc.
   intros. unfold ceval.
   + unfold T_plus.

   intros ; unfold ceval_lifted ; 
  unfold ceval' ; simpl ; try contradiction.
  - destruct wfc ; unfold T_plus ; simpl ; try contradiction.
    +     *)
  Admitted.



(*------------------------ Generic Rules ------------------------*)

(* ONE Rule:

    -----------------
      <phi> 1 <phi>

*)

Theorem OL_One : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex) 
  (phi : assertion Ex),
    (* <phi> skip Ex Ext <phi>. *)
    outcome_triple Ex Ext phi CSkip (wf_skip Ex) phi.
Proof.
  intros. unfold outcome_triple. intros. unfold ceval_lifted ; unfold ceval'. 
  simpl. rewrite (bind_with_unit Ex Ext). apply H.
Qed. 

Theorem OL_Seq : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex) 
  (P Q R : assertion Ex) (c1 c2 : com) (wfc1 : wf_com Ex c1) (wfc2 : wf_com Ex c2),
    (* <phi> skip Ex Ext <phi>. *)
    outcome_triple Ex Ext P c1 wfc1 Q ->
    outcome_triple Ex Ext Q c2 wfc2 R ->
    outcome_triple Ex Ext P (CSeq c1 c2) (wf_seq Ex c1 c2 wfc1 wfc2) R.
Proof.
  intros. unfold outcome_triple in *. intros. unfold ceval_lifted in * ; unfold ceval' in *.
  simpl. rewrite <- (bind_composition Ex Ext). apply H in H1. 
  apply H0 in H1. apply H1.
Qed.

Theorem OL_Div : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex) 
  (phi : assertion Ex),
    (* <phi> skip Ex Ext <phi>. *)
    outcome_triple Ex Ext phi CDiv (wf_div Ex) (T_plus Ex).
Proof.
  intros. unfold outcome_triple. intros. unfold ceval_lifted ; unfold ceval'. 
  simpl. unfold T_plus. 
Qed. 
