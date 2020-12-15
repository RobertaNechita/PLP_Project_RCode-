
Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.

Scheme Equality for string.

Inductive ValueType:=
|default:   ValueType
|undef :   ValueType
|nat_val:   nat -> ValueType
|bool_val : bool -> ValueType
|string_val : string -> ValueType.

Coercion nat_val : nat >-> ValueType.
Coercion bool_val : bool >-> ValueType.
Coercion string_val : string >-> ValueType.

(*tests*)
Compute (nat_val 10).
Compute (string_val "x").

Scheme Equality for ValueType.

(*enviorment ce realizeaza maparea de la un string->type dorit*)
Definition ENV := string -> ValueType.

(*initial toate variabilele  primesc valoarea default*)
Definition env : ENV := fun x => undef.

Compute (env "A").

(*Definition declaration : ( x : string) ( env : Env) :=
 if (ValueType_beq (env x) undef)
     then false
     else true.
  *)
(*UPDATE enviorment*)
(*Definition update (env : ENV) ( a : string ) (val : result) : ENV :=
 fun b =>
         if( eqb b a)
           if(andb (env y) b()
*)
(*incercare de implementare*)
Inductive Memory :=
|mem_init: Memory 
|offset: nat -> Memory. (*indica zonele de memorie a numerelor*) 



Inductive AExp :=
| anum : nat -> AExp
| avar : ValueType -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 50).
Notation "A -' B" := (amin A B) (at level 50).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 46).

Coercion anum : nat >-> AExp.



Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.

Notation "'!' A" := (bnot A ) (at level 52, left associativity).
Notation "A & B" := (band A B) (at level 53 , left associativity).
Notation "A | B" := (bor A B)  (at level 54 , left associativity).
Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bgreaterthan A B) (at level 70).



Inductive Stmt :=
|natdec_ : string ->AExp -> Stmt
|booldec_ : string ->BExp -> Stmt
|assig_ : ValueType -> AExp -> Stmt
|sequence_ : Stmt -> Stmt -> Stmt 
|while_ : BExp -> Stmt -> Stmt
|if_then_ :  BExp -> Stmt -> Stmt 
|if_then_else_ : BExp -> Stmt -> Stmt -> Stmt
|for_ : Stmt -> BExp -> Stmt -> Stmt ->Stmt
|switch_case : Stmt -> BExp -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).

