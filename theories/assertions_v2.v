Require Import examples.
Require Import partial.
Require Import commands.
From Coq Require Import Ensembles.
From Coq Require Import Logic.FunctionalExtensionality.


Definition assertion (Ex : exec_model_consts) := M Ex state -> Prop.

(* Define the monadic lifting of denotational semantics (ceval) *)
Definition ceval_lifted (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (c : com Ex) (st : M Ex state) :=
  bind Ex st (ceval Ex Ext c).

Definition outcome_triple (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (phi : assertion Ex) (c : com Ex) (psi : assertion Ex) := 
  forall (m : M Ex state),
  phi m -> psi (ceval_lifted Ex Ext c m).

(* Notations *)
Declare Scope OL_scope.
Open Scope OL_scope.

Notation "< phi > c Ex Ext < psi >" :=
  (outcome_triple Ex Ext phi c psi) (at level 90, psi at next level)
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

Definition OrOC (Ex : exec_model_consts)  (P Q : assertion Ex) : assertion Ex :=
  fun (m : M Ex state) => P m \/ Q m.

Definition OPlus (Ex : exec_model_consts) (P Q : assertion Ex) : assertion Ex := 
  fun (m : M Ex state) => exists (m1 m2 : M Ex state) H, 
  ap (bop Ex state) m1 m2 H = m /\ P m1 /\ Q m2.

Definition ImpliesOC (Ex : exec_model_consts) (P Q : assertion Ex) : assertion Ex :=
  fun (m : M Ex state) => forall (m': M Ex state), m = m' -> P m' -> Q m'.

Definition AtomicAssn (Ex : exec_model_consts) (P : M Ex state -> Prop) : assertion Ex :=
  fun (m : M Ex state) => P m.

(* Defining inference rules *)
Inductive rule (Ex : exec_model_consts) (Ext : exec_model_theory Ex) :
  (assertion Ex) -> (com Ex) -> (assertion Ex) -> Prop :=
  (* | zero_rule : forall (P : assertion Ex), rule Ex Ext P (CDiv Ex) (T_plus Ex) *)
  | one_rule : forall (P : assertion Ex), rule Ex Ext P (CSkip Ex) P
  | seq_rule : forall (P Q R : assertion Ex) (c1 c2 : com Ex),
                rule Ex Ext P c1 Q -> rule Ex Ext Q c2 R ->
                rule Ex Ext P (CSeq Ex c1 c2) R
  | split_rule : forall (P1 Q1 P2 Q2 : assertion Ex) (c : com Ex),
                  rule Ex Ext P1 c Q1 -> rule Ex Ext P2 c Q2 ->
                  rule Ex Ext (OPlus Ex P1 P2) c (OPlus Ex Q1 Q2)
  | empty_rule : forall (c : com Ex), rule Ex Ext (T_plus Ex) c (T_plus Ex)
  | true_rule : forall (P : assertion Ex) (c : com Ex), 
                  rule Ex Ext P c (Top Ex)
  | false_rule : forall (P : assertion Ex) (c : com Ex),
                  rule Ex Ext (Bot Ex) c P
  | consequence_rule : forall (P' P Q Q' : assertion Ex) (c : com Ex),
                    (forall (m : M Ex state), ImpliesOC Ex P' P m) ->
                    rule Ex Ext P c Q ->
                    (forall (m : M Ex state), ImpliesOC Ex Q Q' m) ->
                    rule Ex Ext P' c Q'
  | plus_rule_total : forall (P Q1 Q2 : assertion Ex) (c1 c2 : com Ex) (pf : is_total Ex),
                      rule Ex Ext P c1 Q1 -> rule Ex Ext P c2 Q2 ->
                      rule Ex Ext P (CPlus_total Ex c1 c2 pf) (OPlus Ex Q1 Q2)
  | plus_rule : forall (P Q1 Q2 : assertion Ex) (e1 e2 : vexp) (c1 c2 : com Ex)
                  (pf : compatible e1 e2),
                  rule Ex Ext P (CSeq Ex (CAssume Ex e1) c1) Q1 -> 
                  rule Ex Ext P (CSeq Ex (CAssume Ex e2) c2) Q2 ->
                  rule Ex Ext P (CPlus Ex e1 e2 c1 c2 pf) (OPlus Ex Q1 Q2).


(*---------------- Soundness of Inference Rules ----------------*)
(* We now begin proving the soundness of Outcome Logic. To begin,
   we show that the conclusion of every inference rule is a valid
   outcome triple given the premises and vice versa. *)

(* Lemma assume_to_plus : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (e1 e2 : vexp) (c1 c2 : com Ex) (m : M Ex state) (pf : compatible e1 e2) {H},
  ap (bop Ex state) (bind Ex m (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1)))
  (bind Ex m (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1))) H = 
  bind Ex m (ceval Ex Ext (CPlus Ex e1 e2 c1 c2 pf)).
Proof.
  intros.  *)

Lemma compatible_addition_defined : forall (Ex : exec_model_consts)
  (Ext : exec_model_theory Ex) (e1 e2 : vexp) (c1 c2 : com Ex)
  (pf : compatible e1 e2) (st : state) ,
  exec_partial Ex state
  (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st)
  (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st).
Proof.
  intros. unfold compatible in pf. specialize (pf st).
  destruct pf ; apply (bop_id_defined Ex Ext).
  - left. simpl. rewrite H. apply (preserve_bind2 Ex Ext).
  - right. simpl. rewrite H. apply (preserve_bind2 Ex Ext).
Qed.


Theorem OL_sound : forall (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (P Q : assertion Ex) (c : com Ex),
  rule Ex Ext P c Q -> outcome_triple Ex Ext P c Q.
Proof.
  intros. induction H ; unfold outcome_triple in * ; intros ; 
  unfold ceval_lifted in * ; simpl.
  - rewrite (bind_with_unit Ex Ext). apply H.
  - rewrite <- (bind_composition Ex Ext). apply IHrule1 in H1. 
    apply IHrule2 in H1. apply H1.
  - unfold OPlus in *. inversion H1. inversion H2. inversion H3. clear H1 H2 H3.
    destruct H4. destruct H2. remember (ceval_lifted Ex Ext c x) as m1. 
    remember (ceval_lifted Ex Ext c x0) as m2. exists m1. exists m2. 
    assert (exists (pf : exec_partial Ex state m1 m2), bind Ex (ap (bop Ex state) x x0 x1) (ceval Ex Ext c) 
              = ap (bop Ex state) m1 m2 pf).
      { subst. unfold ceval_lifted. apply (preserve_bind1 Ex Ext). }
    rewrite H1 in H4. inversion H4. exists x2.
    split ; try split.
    + symmetry. easy.
    + subst. apply IHrule1 in H2. apply H2.
    + subst. apply IHrule2 in H3. apply H3.
  - unfold T_plus in *. rewrite H. rewrite (preserve_bind2 Ex Ext) ; easy.
  - unfold Top. easy.
  - unfold Bot in H. easy.
  - unfold ImpliesOC in *. apply H with (m := m) in H2. apply IHrule in H2. 
    apply H1 with (m := bind Ex m (ceval Ex Ext c)) in H2. apply H2. 
    reflexivity. reflexivity.
  - unfold OPlus. assert (Q2 (bind Ex m (ceval Ex Ext c2))). 
      { apply IHrule2. apply H1. } apply IHrule1 in H1. 
    remember (ceval_lifted Ex Ext c1 m) as m1. 
    remember (ceval_lifted Ex Ext c2 m) as m2.
    exists m1. exists m2.
    assert (exists H, ap (bop Ex state) m1 m2 H = 
        bind Ex m (fun st => ap (bop Ex state) ((ceval Ex Ext c1) st) 
        ((ceval Ex Ext c2) st)  (commands.ceval_obligation_1 ceval Ex Ext st c1 c2 pf))).
        { intros. subst. apply (preserve_bind3 Ex Ext). }
    inversion H3. exists x. split. apply H4. split.
      + subst. unfold ceval_lifted. apply H1.
      + subst. unfold ceval_lifted. apply H2.
  - unfold OPlus. unfold compatible in pf. eexists. eexists.

    specialize (compatible_addition_defined Ex Ext e1 e2 c1 c2 pf). intros.

    assert (exists H', ap (bop Ex state) 
      (bind Ex m (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1)))
      (bind Ex m (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2))) H' =
      bind Ex m (fun st => ap (bop Ex state) 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st) 
      (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st) (H2 st))).
      { apply (preserve_bind3 Ex Ext). }
  
  inversion H3.

  exists x.
  split ; try split.
  2: apply IHrule1. 2: apply H1.  
  2: apply IHrule2. 2: apply H1.

  rewrite H4. assert ((fun (st : state) => ap (bop Ex state) 
    (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e1)) c1) st)
    (ceval Ex Ext (CSeq Ex (CAtom Ex (CAssume Ex e2)) c2) st) (H2 st)) = 
    (fun (st : state) => ceval Ex Ext (CPlus Ex e1 e2 c1 c2 pf) st)).

    (* Is there a way to do this w/o funcitonal extensionality? *)
    { apply functional_extensionality. intros. apply compatible_ceval_plus_rev. }

    rewrite H5. simpl. reflexivity.
Qed.


(*--------------------- Subsumption of Hoare Logic ---------------------*)

(* Before proving that OL subsumes Hoare Logic, we first need to define
   the notions of under-approximation and partial correctness *)

(* Partial correctness *)
Definition pc (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (P : assertion Ex) (c : com Ex) (Q : assertion Ex) :=
  outcome_triple Ex Ext P c (OrOC Ex Q (T_plus Ex)).

(* We will now show that OL, when instantiated using the powerset monad,
   subsumes Hoare Logic *)

Definition PS := powerset_exec_model.
Definition PSt := powerset_exec_model_theory.

Definition hoare_triple (P : state -> Prop) (c : com PS) (Q : state -> Prop) :=
  forall (st st': state),
  P (st) -> In state (ceval PS PSt c st) st' -> Q (st').

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, P at next level)
  : OL_scope.


(* Defining atomic assertions for the powerset model *)
Definition atomic_powerset (P : state -> Prop) : assertion PS :=
  fun (A : Ensemble state) => Inhabited state A  /\
    forall (x : state), In state A x -> P x.


(* Proving subsumption of Hoare Logic *)

Lemma apply_f_to_uninhabited : forall (A B : Type) (U : Ensemble A) (f : A -> Ensemble B),
  ~ Inhabited A U -> ~ Inhabited B (apply_f U f).
Proof.
  intros. unfold apply_f. unfold not in *. intros. apply H. inversion H0.
  inversion H1. destruct H2. econstructor. apply H2.
Qed.

Lemma ap_union : forall (U T : Ensemble state) (pf : exec_partial PS state U T),
  ap (partial_union state) U T pf = Union state U T. 
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included. 
  split ; intros.
  - unfold In in *. unfold partial_union in H. unfold make_partial in H.
    unfold ap in H. easy.
  - unfold In in *. unfold partial_union. unfold make_partial. unfold ap. easy.
Qed. 


Lemma assume_inhabited_or_not : forall (e : vexp) (U : Ensemble state),
  Inhabited state U -> 
  Inhabited state (apply_f U (ceval PS PSt (CAtom PS (CAssume PS e)))) \/
  not (Inhabited state (apply_f U (ceval PS PSt (CAssume PS e)))).
Proof.
  intros. simpl. inversion H. unfold In in H0. destruct (veval x e) eqn:res.
  - left. unfold apply_f. exists x. exists x. split. apply H0. rewrite res.
    apply In_singleton.
  - destruct b.
    + unfold apply_f. left. eexists. exists x. split. apply H0. unfold In.
      rewrite res. apply In_singleton.
    + 

Admitted.

Lemma seq_inhabited_or_not : forall (U : Ensemble state) (c1 c2 : com PS),
  Inhabited state U -> 
  (forall U', Inhabited state U' -> 
    Inhabited state (apply_f U' (ceval PS PSt c1)) \/ 
    not (Inhabited state (apply_f U' (ceval PS PSt c1)))) ->
  (forall U', Inhabited state U' -> 
    Inhabited state (apply_f U' (ceval PS PSt c2)) \/ 
    not (Inhabited state (apply_f U' (ceval PS PSt c2)))) ->
  Inhabited state (apply_f U (ceval PS PSt (CSeq PS c1 c2))) \/ 
    not (Inhabited state (apply_f U (ceval PS PSt (CSeq PS c1 c2)))).
Proof.
  intros. apply H0 in H. destruct H.
  + apply H1 in H. destruct H.
    * left. simpl. rewrite <- (bind_composition PS PSt). apply H.
    * right. simpl.  rewrite <- (bind_composition PS PSt). apply H.
  + right. simpl. rewrite <- (bind_composition PS PSt). apply apply_f_to_uninhabited.
    apply H.
Qed.
  

Lemma apply_f_inhabited: forall (U : Ensemble state) (c : com PS),
  Inhabited state U -> Inhabited state (apply_f U (ceval PS PSt c)) \/  
  not (Inhabited state (apply_f U (ceval PS PSt c))).
Proof.
  intros. generalize dependent U. induction c ; intros.
  - simpl. right. unfold not. intros. unfold apply_f in H0. inversion H0. 
    unfold In in H1. inversion H1. inversion H2. contradiction.
  - left. inversion H. unfold apply_f. simpl. unfold In. exists x.
    unfold In in H0. unfold In. exists x. split ; auto. constructor.
  - apply seq_inhabited_or_not ; easy.
  - assert (H' := H). apply IHc1 in H. apply IHc2 in H'. destruct H.
    + left. simpl. unfold apply_f. unfold In. inversion H. unfold apply_f in H0.
      unfold In in H0. inversion H0. destruct H1. exists x. unfold In. exists x0.
      split. apply H1. rewrite ap_union. apply Union_introl. apply H2.
    + destruct H'.
      * left. simpl. unfold apply_f. unfold In. inversion H0. unfold apply_f in H1.
        unfold In in H1. inversion H1. destruct H2. exists x. unfold In. exists x0.
        split. apply H2. rewrite ap_union. apply Union_intror. apply H3.
      * right. unfold not. unfold not in H. unfold not in H0. intros. inversion H1.
        unfold In in H2. unfold apply_f in H2. unfold In in H2. inversion H2.
        destruct H3. simpl in H4. rewrite ap_union in H4. destruct H4. 
        -- apply H. unfold apply_f. exists x. unfold In. exists x0. split. 
           apply H3. apply H4.
        -- apply H0. unfold apply_f. exists x. unfold In. exists x0. split.
           apply H3. apply H4.
  - specialize (compatible_addition_defined PS PSt e1 e2 c1 c2 pf). intros.
    assert (ceval PS PSt (CPlus PS e1 e2 c1 c2 pf) = 
      fun st => ap (bop PS state) 
      (ceval PS PSt (CSeq PS (CAtom PS (CAssume PS e1)) c1) st)
      (ceval PS PSt (CSeq PS (CAtom PS (CAssume PS e2)) c2) st) (H0 st)).
      { apply functional_extensionality. intros. 
        rewrite compatible_ceval_plus_rev with (compat := pf). reflexivity. }
      rewrite H1.

    remember (ceval PS PSt (CSeq PS (CAtom PS (CAssume PS e1)) c1)) as f1.
    remember (ceval PS PSt (CSeq PS (CAtom PS (CAssume PS e2)) c2)) as f2.

    specialize (preserve_bind3 PS PSt state state f1 f2 U H0). intros.
    inversion H2. simpl in H3. simpl. rewrite <- H3. rewrite ap_union.
    clear H3 x H2 H1 H0.
    
    specialize (assume_inhabited_or_not e1) as He1. 
    specialize (assume_inhabited_or_not e2) as He2.
    specialize (seq_inhabited_or_not U (CAtom PS (CAssume PS e1)) 
      c1 H He1 IHc1) as Hguard1. 
    specialize (seq_inhabited_or_not U (CAtom PS (CAssume PS e2)) 
      c2 H He2 IHc2) as Hguard2.
    
    destruct Hguard1.
    + left. inversion H0. exists x. subst f1. apply Union_introl. apply H1.
    + destruct Hguard2 ; subst f2.
      * left. inversion H1. exists x. apply Union_intror. apply H2.
      * right. unfold not. intros. inversion H2. inversion H3.
        subst f1. unfold not in H0. apply Inhabited_intro in H4. apply H0 in H4.
        apply H4.
        unfold not in H1. apply Inhabited_intro in H4. apply H1 in H4. apply H4.
    
  - destruct c.
    + apply assume_inhabited_or_not. apply H.
    + unfold apply_f. inversion H. unfold In in *. left. eexists. exists x0.
      split. apply H0. simpl. apply In_singleton.
Qed.  


Lemma not_inhabited_empty : forall (A : Type) (U : Ensemble A),
  not (Inhabited A U) -> U = Empty_set A.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split.
  - unfold Included. intros. unfold not in H. exfalso. apply H. econstructor.
    apply H0.
  - unfold Included. intros. unfold not in H. unfold In in H0. contradiction.
Qed. 

Lemma inhabited_not_empty : forall (A : Type) (U : Ensemble A),
  Inhabited A U -> U <> Empty_set A.
Proof.
  intros. unfold not. intros. subst. inversion H. inversion H0.
Qed.

(* Now proving the theorem itself *)
Theorem OL_subsumes_HL : forall (P Q : state -> Prop) (c : com PS),
  hoare_triple P c Q <-> pc PS PSt (atomic_powerset P) c (atomic_powerset Q).
Proof.
  intros. unfold pc. unfold outcome_triple. unfold hoare_triple. unfold atomic_powerset. split.
  - intros. unfold OrOC. unfold ceval_lifted. simpl. inversion H0.  
    apply apply_f_inhabited with (c := c) in H1.
    destruct H1.
    + left. split. apply H1. intros. unfold apply_f in H3. inversion H3. 
      apply H with (st := x0) (st' := x). apply H2. apply H4. apply H4.
    + right. unfold T_plus.  apply not_inhabited_empty in H1. rewrite H1.
      reflexivity.
  - intros. assert (atomic_powerset P (Singleton state st)).
      { unfold atomic_powerset. split. assert (In state (Singleton state st) st).
        {  apply In_singleton. } apply Inhabited_intro in H2. apply H2. intros.
        inversion H2. rewrite <- H3. easy. }
    apply H in H2. unfold OrOC in H2. destruct H2. 

    (* Case where C[{st}] |= Q *)
    + destruct H2. apply H3. simpl. unfold In. unfold apply_f. exists st. split.
      apply In_singleton. apply H1.

    (* Case where C[{st}] |= T^+ *)
    + unfold T_plus in H2. simpl in H2. unfold apply_f in H2. 
      assert ((ceval PS PSt c st) = Empty_set state). 
      { rewrite <- H2. apply Extensionality_Ensembles. unfold Same_set. split.
        - unfold Included. intros. unfold In. exists st. split. apply In_singleton.
          unfold In in H3. apply H3.
        - unfold Included. intros. unfold In. destruct H3. destruct H3.
          inversion H3. subst. unfold In in H4. apply H4. }
      apply Inhabited_intro in H1. apply inhabited_not_empty in H1. contradiction.
Qed.


(* -------------------- Subsumption of Lisbon Logic -------------------- *)
(* We will now show that OL subsumes Lisbon Logic. For this, we will re-use
   some of the definitions from the above section along with some new ones.
   most notably, we describe the semantics of a triple in Lisbon Logic: *)
      
(* Under-approximation *)
Definition under (Ex : exec_model_consts) (Ext : exec_model_theory Ex)
  (P : assertion Ex) (c : com Ex) (Q : assertion Ex) :=
  outcome_triple Ex Ext P c (OPlus Ex Q (Top Ex)).

Definition lisbon_triple (P : state -> Prop) (c : com PS) (Q : state -> Prop) :=
  forall st,
  P (st) -> exists st', In state (ceval PS PSt c st) st' /\ Q (st').


Lemma ceval_linear : forall (X Y Z : M PS state) (c : com PS) {H},
  Union state X Y = Z -> 
  ap (bop PS state) (ceval_lifted PS PSt c X) (ceval_lifted PS PSt c Y) H =
  ceval_lifted PS PSt c Z.
Proof.
  intros. unfold ceval_lifted. rewrite <- H0.
  assert (exists H, ap (bop PS state) X Y H = Union state X Y).
    { eexists. reflexivity. }
  inversion H1. rewrite <- H2. 
  assert (exists H, bind PS (ap (bop PS state) X Y x) (ceval PS PSt c) = 
                    ap (bop PS state) (bind PS X (ceval PS PSt c)) 
                    (bind PS Y (ceval PS PSt c)) H).
    { apply (preserve_bind1 PS PSt). }
  inversion H3. rewrite H4. reflexivity. 
  Unshelve. simpl. unfold powerset_partial. tauto.
Qed.


Lemma exists_satisfies_under : forall (X : Ensemble state) (P : state -> Prop),
  OPlus PS (atomic_powerset P) (Top PS) X <-> exists x, In state X x /\ P x.
Proof.
  intros. split.
  - intros. unfold OPlus in H. inversion H. inversion H0. inversion H1. 
    destruct H2. destruct H3. unfold atomic_powerset in H3. destruct H3.
    inversion H3. exists x2. 
    assert (X = Union state x x0).
      { rewrite <- H2. reflexivity. } 
    split. rewrite H7. apply Union_introl. apply H6. apply H5. apply H6.
  - intros. inversion H. destruct H0. unfold OPlus. 
    remember (Singleton state x) as s. exists s. exists X. exists I. split.
    + assert (ap (bop PS state) s X I = Union state s X).
        { simpl. reflexivity. }
      rewrite H2. apply Extensionality_Ensembles. unfold Same_set. unfold Included.
      split.
      * intros. destruct H3. subst. inversion H3. rewrite <- H4. apply H0. apply H3.
      * intros. apply Union_intror. apply H3.
    + split. unfold atomic_powerset.
      * split. assert (In state s x). { subst. apply In_singleton. } 
        apply Inhabited_intro in H2. apply H2. intros. subst. inversion H2.
        rewrite <- H3. apply H1.
      * unfold Top. tauto.
Qed.


Lemma PS_bop_union : forall (X Y : Ensemble state) {H},
  ap (bop PS state) X Y H = Union state X Y.
Proof. 
  intros. simpl. reflexivity.
Qed.


Lemma apply_f_singleton : forall (st : state) (f : state -> Ensemble state),
  apply_f (Singleton state st) f = f st.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. unfold Included.
  unfold apply_f.
  split ; intros.
  - inversion H. destruct H0. inversion H0. apply H1.
  - exists st. split. apply In_singleton. apply H.
Qed.


Theorem OL_subsumes_LL : forall (P Q : state -> Prop) (c : com PS),
  lisbon_triple P c Q <-> under PS PSt (atomic_powerset P) c (atomic_powerset Q).
Proof.
  intros. unfold under. unfold outcome_triple. unfold lisbon_triple. split.
  (* Forwards Direction *)
  - intros. destruct H0. inversion H0. specialize (H1 x H2). 
    specialize (H x H1). inversion H. destruct H3. remember (Singleton state x) as s.
    apply exists_satisfies_under. exists x0. split.
    + assert (Union state s m = m).
        { subst. apply Extensionality_Ensembles. unfold Same_set. unfold Included.
          split ; intros. destruct H5. subst. inversion H5. rewrite <- H6. 
          apply H2. apply H5. apply Union_intror. apply H5. }
      assert (ap (bop PS state) (ceval_lifted PS PSt c s) (ceval_lifted PS PSt c m) I =
              (ceval_lifted PS PSt c m)).
        { apply ceval_linear. apply H5. }
      rewrite <- H6.
      assert (ceval PS PSt c x = ceval_lifted PS PSt c s ).
            { rewrite <- apply_f_singleton. simpl. subst. reflexivity. }
      rewrite <- H7.  rewrite PS_bop_union. apply Union_introl. easy.
    + apply H4.
  (* Backwards Direction *)
  - intros. remember (Singleton state st) as s.
    specialize (H s). assert (atomic_powerset P s).
      { unfold atomic_powerset. split. assert (In state s st). subst. 
        apply In_singleton. apply Inhabited_intro in H1. apply H1.
        intros. subst. inversion H1. rewrite <- H2. apply H0. }
    apply H in H1. apply exists_satisfies_under in H1. inversion H1. destruct H2.
    exists x. split.
    + rewrite <- apply_f_singleton. unfold ceval_lifted in H2. simpl in H2.
      subst. apply H2.
    + apply H3. 
Qed.