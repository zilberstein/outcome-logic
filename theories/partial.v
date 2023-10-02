From Coq Require Import ssreflect ssrfun ssrbool.
Unset Printing Implicit Defensive.

Require Import Coq.Init.Datatypes.
Require Import Coq.Relations.Relation_Definitions.

Definition partial_fun {A} (R : relation A) B : Type :=
  { p : A * A | R (fst p) (snd p) } -> B.

Definition make_partial {A B R} (f : A -> A -> B) : partial_fun R B :=
  fun arg =>
    match arg with
      exist _ (x, y) _ => f x y
    end.

Definition is_def {A B : Type} {R : relation A} (f : partial_fun R B) (x y : A) : Prop :=
  exists pf (z : B), f (exist (fun p => R (fst p) (snd p)) (x, y) pf) = z.

Lemma is_def_refl : forall A B (R : rel A) (f : partial_fun R B) x,
    reflexive _ R ->
    is_def f x x.
Proof.
  intros; exists (H x); eexists _; reflexivity.
Qed.  

Lemma is_def_sym : forall A B (R : relation A) (f : partial_fun R B) x y,
    symmetric _ R ->
    is_def f x y ->
    is_def f y x.
Proof.
  intros A B R f x y Hsym His_def.
  inversion His_def as [HR _]; simpl in HR.
  apply Hsym in HR.
  exists HR. eexists _. reflexivity.
Qed.

Lemma is_def_trans : forall A B (R : relation A) (f : partial_fun R B) x y z,
    transitive _ R ->
    is_def f x y ->
    is_def f y z ->
    is_def f x z.
Proof.
  intros. inversion H0 as [Hr1 _]. inversion H1 as [Hr2 _]. simpl in *.
  exists (H _ _ _ Hr1 Hr2). eexists; reflexivity.
Qed.  

Definition ap {A B} {R : relation A} (f : partial_fun R B) (x y : A) : (R x y) -> B.
  intro Hr. apply f. constructor 1 with (x,y); simpl. trivial.
Defined.

Definition get_is_def_pf {A B} R f x y : @is_def A B R f x y -> R x y.
  intro Hdef. inversion Hdef as [pf _]. trivial.
Defined.

Definition total_fun A B : Type := partial_fun (fun (_ _ : A) => True) B.

Lemma is_def_total : forall A B (f : total_fun A B) x y,
    is_def f x y.
Proof.
  intros; exists I; eexists; reflexivity.
Qed.

Definition applyT {A B} (f : total_fun A B) (x y : A) : B := ap f x y I.

(* EXAMPLE -- BOOLEAN PLUS *)

Definition bool_compat : relation bool :=
  fun x y => ~ (x = true /\ y = true).

Definition bool_add : partial_fun bool_compat bool :=
  make_partial (fun x y => orb x y).

Lemma bool_compat_symmetric : symmetric _ bool_compat.
Proof.
  intros x y; unfold bool_compat; intros H Hcontra. apply H; apply and_comm; trivial.
Qed.

Lemma compat_true_l : forall x,
    bool_compat x true -> x = false.
Proof.
  intros. destruct x.
  - contradict H. unfold bool_compat. intros Hnot. apply Hnot; auto.
  - trivial.
Qed.

Lemma compat_true_r : forall x,
    bool_compat true x -> x = false.
Proof.
  intros. apply bool_compat_symmetric in H. apply compat_true_l; trivial.
Qed.
 
Lemma bool_compat_assoc : forall x y z (Hxy : bool_compat x y) (Hz : bool_compat (ap bool_add x y Hxy) z),
  exists Hyz Hx,
    ap bool_add (ap bool_add x y Hxy) z Hz = ap bool_add x (ap bool_add y z Hyz) Hx.
Proof.
  intros.
  assert (Hyz : bool_compat y z).
  { intros [ -> -> ]. apply Hz. assert (x = false) by (apply (compat_true_l x Hxy)).
    subst. auto.
  }
  assert (Hx : bool_compat x (ap bool_add y z Hyz)).
  { intros [ -> Hadd ]. assert (y = false) by (apply (compat_true_r _ Hxy)); subst; auto. }
  exists Hyz; exists Hx. destruct x; auto.
Qed.
