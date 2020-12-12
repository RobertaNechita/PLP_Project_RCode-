
(* Sintaxa limbajului RCode++ *)

Require Import String.
Local Open Scope string_scope.
Scheme Equality for string.

(* Declararea tipurilor de variabile  *)
Inductive ValueType :=
| undef : ValueType
| nat_val : nat -> ValueType
| bool_val : bool -> ValueType
| string_val : string -> ValueType. 


Scheme Equality for ValueType.

Inductive AExp := 
| anum : nat -> AExp
| avar : ValueType -> AExp
| aplus : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (asub A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).

Coercion anum : nat >-> AExp.
Coercion avar : ValueType >-> AExp.

(*Enviorments*)
Definition Env := ValueType -> nat.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.
