Require Import commands.
Require Import partial.
Require Import Coq.Relations.Relation_Definitions.

(* Since proving OL Subsumes Hoare Logic requires case analysis on the result of
[|C|], we try a definition of the powerset monad using an inductive definition
of sets *)

(* Definition of a set  - either the emptyset, a singleton set, or the union of
two sets *)
Inductive ind_set (A : Type) : Type :=
| Emptyset
| Singleton (x : A)
| Union (B C : ind_set A).

(* Next, we define a way to decide whether an element is contained in a set *)
Inductive In_ind {A : Type} (x : A) : ind_set A -> Prop :=
| in_emptyset : False -> In_ind x (Emptyset A)
| in_singleton : In_ind x (Singleton A x)
| in_union : forall (B C : ind_set A), 
              In_ind x B \/ In_ind x C -> In_ind x (Union A B C).

(* Now, we can define the necessary pieces for creating an execution model 
over these inductive sets: *)
Fixpoint apply_fun {A B : Type} (s : ind_set A) (f : A -> ind_set B) : ind_set B :=
  match s with
  | Emptyset _ => Emptyset B
  | Singleton _ x => f x
  | Union _ C D => Union B (apply_fun C f) (apply_fun D f)
  end.
  
Definition ind_set_partial : forall (A : Type), relation (ind_set A) :=
  fun (A : Type) (x y : ind_set A) => True.

Definition partial_union : forall (A : Type), total_fun (ind_set A) (ind_set A) :=
  fun (A : Type) => make_partial (fun (x y : ind_set A) => (Union A) x y).

Definition ind_powerset_EM :=
  {|
    M := ind_set;
    bind := @apply_fun;
    unit := fun (A:Type) (x:A) => Singleton A x;
    exec_partial := ind_set_partial;
    bop := partial_union;
    id := fun (A : Type) => Emptyset A
  |}.


(* Next, we must prove that the necessary axioms hold *)

(* NOTE: We admit these for now. If it turns out that this does allow us to 
   prove the subsumption of Hoare Logic, then we will return and complete the
   proofs. *)

Definition ind_PS := ind_powerset_EM.

(* Lemmas *)

Lemma union_comm : forall (U : Type) (B C : ind_set U),
  Union U B C = Union U C B.
Proof.
  Admitted.

Lemma union_assoc : forall (U : Type) (B C D : ind_set U),
  Union U B (Union U C D) = Union U (Union U B C) D.
Proof.
  Admitted.

Lemma emptyset_id : forall (U : Type) (A : ind_set U),
  Union U A (Emptyset U) = A.
Proof.
  Admitted.

(* Proof of axioms *)

Theorem ind_set_bop_comm : forall (A : Type) (x y : (M ind_PS) A) 
  (Hxy : exec_partial ind_PS A x y), 
  exists Hyx, 
  ap (bop ind_PS A) x y Hxy = ap (bop ind_PS A) y x Hyx.
Proof.
 Admitted.

Theorem ind_set_bop_assoc : forall (A : Type) (x y z : (M ind_PS) A) 
  (Hyz : exec_partial ind_PS A y z) (Hx_yz : exec_partial ind_PS A x (ap (bop ind_PS A) y z Hyz)),
  exists Hxy Hxy_z,
  ap (bop ind_PS A) x (ap (bop ind_PS A) y z Hyz) Hx_yz = 
  ap (bop ind_PS A) (ap (bop ind_PS A) x y Hxy) z Hxy_z.
Proof.
  Admitted.

Theorem ind_set_id : forall (A : Type) (x : (M ind_PS) A) ,
  exists (Hx : exec_partial ind_PS A x (id ind_PS A)), ap (bop ind_PS A) x (id ind_PS A) 
  Hx = x.
Proof.
  Admitted.

(* Proving that the PCM preserves the monad bind: *)

Theorem ind_set_preserve_bind1 : forall (A B: Type) (f : A -> (M ind_PS) B) 
  (x y : (M ind_PS) A) (Hxy : exec_partial ind_PS A x y), 
  exists Hbind,
  bind ind_PS (ap (bop ind_PS A) x y Hxy) f = 
  ap (bop ind_PS B) (bind ind_PS x f) (bind ind_PS y f) Hbind.
Proof.
  Admitted.

Theorem ind_set_preserve_bind2 : forall (A B : Type) (f : A -> (M ind_PS) B) 
  (x : (M ind_PS) A), 
  bind ind_PS (id ind_PS A) f = id ind_PS B.
Proof.
  Admitted.
    
 (* Finally, we prove that the monad laws hold *)

Theorem ind_set_bind_with_unit : forall (A : Type) (m : (M ind_PS) A),
  bind ind_PS m (unit ind_PS) = m.
Proof.
  Admitted.

Theorem ind_set_bind_of_unit : forall (A B : Type) (f : A -> (M ind_PS) B) (x : A),
  bind ind_PS (unit ind_PS x) f = f x.
Proof.
  Admitted.

Theorem ind_set_bind_composition : forall (A B C : Type) (f : A -> (M ind_PS) B) 
  (g : B -> (M ind_PS) C) (m : (M ind_PS) A),
  bind ind_PS (bind ind_PS m f) g = bind ind_PS m (fun x => bind ind_PS (f x) g).
Proof.
  Admitted.

Definition ind_set_exec_model_theory := 
  {|
    (* PCM *)
    pcm_comm := ind_set_bop_comm ;
    pcm_assoc := ind_set_bop_assoc ; 
    pcm_id := ind_set_id;

    (* Preservation of monad bind*)
    preserve_bind1 := ind_set_preserve_bind1;
    preserve_bind2 := ind_set_preserve_bind2;

    (* Monad Laws *)
    bind_with_unit := ind_set_bind_with_unit;
    bind_of_unit := ind_set_bind_of_unit;
    bind_composition := ind_set_bind_composition;
  |}.




 