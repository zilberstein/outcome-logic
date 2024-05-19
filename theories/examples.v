Require Import powerset.
Require Import partial.
Require Import commands.
Require Import assertions_v2.
From Coq Require Import Ensembles.

(* Let's begin with some examples using the powerset monad to model 
   non-deterministic evaluation *)

Module powerset_examples.

Definition PS := powerset_exec_model.
Definition PSt := powerset_exec_model_theory.



