Require Import partial.
Require Import commands.
From Coq Require Import Ensembles.
Require Import Coq.Relations.Relation_Definitions.

(* Example: Execution model using powerset monad *)
Definition apply_f {A B : Type} (s : Ensemble A) (f : A -> Ensemble B) : Ensemble B :=
  fun (y : B) => exists (x : A), In A s x /\ In B (f x) y.

Definition powerset_partial : forall (A : Type), relation (Ensemble A) :=
  fun (A : Type) (x y : Ensemble A) => True.

Definition partial_union : forall (A : Type), total_fun (Ensemble A) (Ensemble A) :=
  fun (A : Type) => make_partial (fun (x y : Ensemble A) => (Union A) x y).

Definition powerset_exec_model :=
{|
  M := Ensemble;
  bind := @apply_f;
  unit := fun (A:Type) (x:A) => Singleton A x;
  exec_partial := powerset_partial;
  bop := partial_union;
  id := fun (A : Type) => Empty_set A
|}.

Definition Pe := powerset_exec_model.

(* Now, we prove that this is indeed a valid execution model. First, let us
   prove some lemmas: *)

Lemma union_comm : forall (U : Type) (B C : Ensemble U),
  Union U B C = Union U C B.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split.
  - unfold Included. intros. destruct H.
    + apply Union_intror. easy.
    + apply Union_introl. easy.
  - unfold Included. intros. destruct H.
    + apply Union_intror. easy.
    + apply Union_introl. easy.
Qed.

Lemma apply_f_union : forall (U W : Type) (A B : Ensemble U) (f : U -> Ensemble W),
  apply_f (Union U A B) f = Union W (apply_f A f) (apply_f B f).
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split ; 
  unfold Included ; intros.
  - repeat destruct H.
    + apply Union_introl. unfold apply_f. exists x0. split ; easy.
    + apply Union_intror. unfold apply_f. exists x0. split ; easy.
  - repeat destruct H.
    + unfold apply_f. exists x0. split ; try apply Union_introl ; easy.
    + repeat destruct H. unfold apply_f. exists x0.
      split ; try apply Union_intror ; easy.
Qed. 

Lemma apply_f_empty : forall (U W : Type) (f : U -> Ensemble W),
  apply_f (Empty_set U) f = Empty_set W.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split ; 
  unfold Included ; intros.
  - destruct H. destruct H. contradiction.
  - contradiction.
Qed.

Lemma union_assoc : forall (U : Type) (A B C : Ensemble U),
  Union U A (Union U B C) = Union U (Union U A B) C.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split ; 
  unfold Included ; intros ; destruct H.
  - apply Union_introl. apply Union_introl. easy.
  - destruct H.
    + apply Union_introl. apply Union_intror. easy.
    + apply Union_intror. easy.
  - destruct H.
    + apply Union_introl. easy.
    + apply Union_intror. apply Union_introl. easy.
  - apply Union_intror. apply Union_intror. easy.
Qed.

Lemma emptyset_id : forall (U : Type) (A : Ensemble U),
  Union U A (Empty_set U) = A.
Proof.
  intros. apply Extensionality_Ensembles. unfold Same_set. split ;
  unfold Included ; intros.
  - destruct H ; try easy ; try contradiction.
  - apply Union_introl. easy.
Qed.

(* Proving that < M A, bop, id > forms a PCM for any set A *)

Theorem powerset_bop_comm : forall (A : Type) (x y : (M Pe) A) (Hxy : exec_partial Pe A x y), 
  exists Hyx, 
  ap (bop Pe A) x y Hxy = ap (bop Pe A) y x Hyx.
Proof.
  intros. assert (Hyx : exec_partial Pe A x y). 
    { simpl. unfold powerset_partial. easy. }
  exists Hyx. simpl. unfold partial_union. unfold ap. simpl. apply union_comm.
Qed.

Theorem powerset_bop_assoc : forall (A : Type) (x y z : (M Pe) A) (Hyz : exec_partial Pe A y z) 
(Hx_yz : exec_partial Pe A x (ap (bop Pe A) y z Hyz)),
  exists Hxy Hxy_z,
  ap (bop Pe A) x (ap (bop Pe A) y z Hyz) Hx_yz = 
  ap (bop Pe A) (ap (bop Pe A) x y Hxy) z Hxy_z.
Proof.
  intros. assert (Hxy : exec_partial Pe A x y).
    { simpl. unfold powerset_partial. easy. }
  assert (Hxy_z : exec_partial Pe A (ap (bop Pe A) x y Hxy) z).
    { simpl. unfold powerset_partial. easy. }
  exists Hxy, Hxy_z. simpl. unfold partial_union. unfold ap. simpl.
  apply union_assoc.
Qed.

Theorem powerset_id : forall (A : Type) (x : (M Pe) A) ,
  exists (Hx : exec_partial Pe A x (id Pe A)), ap (bop Pe A) x (id Pe A) 
  Hx = x.
Proof.
  intros. simpl.  unfold partial_union. unfold ap. simpl. exists I. 
  apply emptyset_id.
Qed.

(* Proving that the PCM preserves the monad bind: *)

Theorem powerset_preserve_bind1 : forall (A B: Type) (f : A -> (M Pe) B) 
  (x y : (M Pe) A) (Hxy : exec_partial Pe A x y), 
  exists Hbind,
  bind Pe (ap (bop Pe A) x y Hxy) f = 
  ap (bop Pe B) (bind Pe x f) (bind Pe y f) Hbind.
Proof.
  intros. assert (HBind : exec_partial Pe B (bind Pe x f) (bind Pe y f)).
    { simpl. unfold powerset_partial. easy. }
  exists HBind. simpl. unfold partial_union. unfold ap. simpl. 
  apply apply_f_union.
Qed.

Theorem powerset_preserve_bind2 : forall (A B : Type) (f : A -> (M Pe) B), 
  bind Pe (id Pe A) f = id Pe B.
Proof.
  intros. simpl. apply apply_f_empty.
Qed.
    
 (* Finally, we prove that the monad laws hold *)

 Theorem powerset_bind_with_unit : forall (A : Type) (m : (M Pe) A),
  bind Pe m (unit Pe) = m.
Proof.
  intros. simpl. apply Extensionality_Ensembles. unfold Same_set. split ;
  unfold Included ; intros.
  - repeat destruct H. destruct H0. easy.
  - unfold apply_f. exists x. split ; try simpl ; easy.
Qed.

Theorem powerset_bind_of_unit : forall (A B : Type) (f : A -> (M Pe) B) (x : A),
  bind Pe (unit Pe x) f = f x.
Proof.
  intros. simpl. apply Extensionality_Ensembles. unfold Same_set. split ; 
  unfold Included ; intros.
  - repeat destruct H. easy.
  - unfold apply_f. exists x. split ; try simpl ; easy.
Qed.

Theorem powerset_bind_composition : forall (A B C : Type) (f : A -> (M Pe) B) 
  (g : B -> (M Pe) C) (m : (M Pe) A),
  bind Pe (bind Pe m f) g = bind Pe m (fun x => bind Pe (f x) g).
Proof.
  intros. simpl. apply Extensionality_Ensembles. unfold Same_set. split ;
  unfold Included ; intros.
  - repeat destruct H. unfold apply_f. exists x1. split.
    + easy.
    + exists x0. split ; easy.
  - repeat destruct H. repeat destruct H0. unfold apply_f. exists x1. split.
    + exists x0. split ; easy.
    + easy.
Qed. 


Theorem powerset_preserve_bind3 : forall (A B : Type) (f g : A -> (M Pe) B) (x : (M Pe) A)
(Hfg : forall (y : A), exec_partial Pe B (f y) (g y)),
exists H,
  ap (bop Pe B) (bind Pe x f) (bind Pe x g) H = 
  bind Pe x (fun y => ap (bop Pe B) (f y) (g y) (Hfg y)).
Proof.
Admitted.


(* Now, we have proved all the necessary theorems to prove that this is 
   indeed a valid execution model. *)

Definition powerset_exec_model_theory := 
  {|
    (* PCM *)
    pcm_comm := powerset_bop_comm ;
    pcm_assoc := powerset_bop_assoc ; 
    pcm_id := powerset_id;

    (* Preservation of monad bind*)
    preserve_bind1 := powerset_preserve_bind1;
    preserve_bind2 := powerset_preserve_bind2;
    preserve_bind3 := powerset_preserve_bind3;

    (* Monad Laws *)
    bind_with_unit := powerset_bind_with_unit;
    bind_of_unit := powerset_bind_of_unit;
    bind_composition := powerset_bind_composition;
  |}.





