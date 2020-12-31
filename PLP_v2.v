Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(*       Errnat-constructor util pentru op. aritmetice        *)

Inductive Errnat :=
|error_nat : Errnat
|number : nat ->Errnat.

Coercion number : nat >-> Errnat.

Inductive Errbool :=
|error_bool : Errbool
|boolean : bool ->Errbool.

Coercion boolean : bool >-> Errbool.

Compute (number 4).
Compute (boolean true).

Inductive Errstring :=
|error_string : Errstring
|str : string ->Errstring.

Coercion str : string >-> Errstring.

(*                Operatii pe stringuri             *)

Compute eqb "an" "ax".
Compute eqb "a" "a".

(*        functiile strcat & strlen & strcmp        *)

Fixpoint STRLEN (sir1 : string) : nat :=
match sir1 with
|EmptyString => 0
|String c sir1' => S (STRLEN sir1')
end.

Fixpoint STRCAT (sir1 sir2 : string) : string :=
match sir1 with
|EmptyString => sir2
|String c sir1' => String c ( STRCAT sir1' sir2)
end.

(*                      Notatii                     *)
Notation "strcmp( a , b )" := (eqb a b)(at level 70).
Notation "strcat( a , b )" := (STRCAT a b)(at level 68).
Notation "strlen( a )" := (STRLEN a )(at level 68).

(*                     teste                        *)
Compute strcmp( "plp" , "plp" ).
Compute strcmp( "plp+" , "plp" ).

Compute strcat("plp" , "_project").
Compute strlen( "result.is.12" ).


(*     ValueResult-tip de date ce inglobeaza toate celelalte tipuri utilizate in limbaj      *)

Inductive Value_Result :=
|ERR_undec : Value_Result
|ERR_assign : Value_Result
|DEFAULT : Value_Result
|nat_val : Errnat -> Value_Result
|bool_val : Errbool -> Value_Result
|string_val : Errstring -> Value_Result.



Scheme Equality for Value_Result.
Compute bool_val true.
Compute string_val "plp".

(*                      definirea enviorment-urilor necesare                           *)

(*mapare de la un nume de variabila catre un rezultat*)
Definition Env := string -> Value_Result.

 
(*initial fiecare variabila primeste undeclared status*)
Definition env : Env := fun x => ERR_undec .
Compute (env "plp").


(*functie ce mentine egalitatea peste tipuri*)

Definition check_equality_types (type1 : Value_Result)(type2 : Value_Result) : bool :=
match type1 with
|ERR_undec => match type2 with
              |ERR_undec => true
              | _ => false
              end
|ERR_assign => match type2 with
               |ERR_assign => true
               | _ => false
               end
|DEFAULT => match type2 with
            |DEFAULT => true
            | _ => false
            end
|nat_val v => match type2 with
              |nat_val n => true
              | _ => false
              end
|bool_val v => match type2 with
               |bool_val n => true
               | _ => false
              end
|string_val v => match type2 with
                 |string_val n => true
                 | _ => false
                end  
end.   

(*                              teste                             *)
 
Compute (check_equality_types (nat_val 100)(nat_val 335)).
Compute (check_equality_types (nat_val 100)(bool_val true)).
Compute (check_equality_types (nat_val 100) ERR_undec).
Compute (check_equality_types ERR_assign (bool_val true)).


(*                        functia de UPDATE                      *)
Definition update (env : Env ) ( S : string ) ( v : Value_Result) : Env :=
  fun y =>
   if( eqb y S)
       then 
          if ( andb (check_equality_types ERR_undec (env y)) (negb (check_equality_types DEFAULT v)))
          then ERR_undec 
          else
             if( andb (check_equality_types ERR_undec (env y))  (check_equality_types DEFAULT v))
             then DEFAULT
             else
                 if (orb (check_equality_types DEFAULT (env y)) (check_equality_types v (env y)))
                 then v 
                 else ERR_assign
   else (env y).


(*                              teste                             *)

Compute (env "x").
Compute (update (update env "x" (DEFAULT)) "x" (bool_val true) "x").
Compute (update env "a" (nat_val 100)) "a".

Notation "S [ V \' X ]" := (update S V X) (at level 0).  



(*                         expresii aritmetice                          *)


Inductive AExp :=
| avar: Errstring -> AExp 
| anum: Errnat -> AExp
| aplus: AExp -> AExp -> AExp
| amin: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp 
| amodulo: AExp -> AExp -> AExp.

Coercion anum: Errnat >-> AExp.
Coercion avar: Errstring >-> AExp.


(*                     notatii operatii artimetice                      *)

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (amin A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amodulo A B)(at level 45, left associativity).

 

(*                 functii de calcul operatii aritmetice ce trateaza erori                  *)


Definition plus_ErrorNat (n1 n2 : Errnat) : Errnat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | number v1, number v2 => number (v1 + v2)
    end.


Definition sub_ErrorNat (n1 n2 : Errnat) : Errnat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | number n1, number n2 => if Nat.ltb n1 n2
                        then error_nat
                        else number (n1 - n2)
    end.


Definition mul_ErrorNat (n1 n2 : Errnat) : Errnat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | number v1, number v2 => number (v1 * v2)
    end.


Definition div_ErrorNat (n1 n2 : Errnat) : Errnat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, number 0 => error_nat
    | number v1, number v2 => number (Nat.div v1 v2)
    end.


Definition mod_ErrorNat (n1 n2 : Errnat) : Errnat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, number 0 => error_nat
    | number v1, number v2 => number (v1 - v2 * (Nat.div v1 v2))
    end.


(*                 teste                      *)
Compute ( plus_ErrorNat 5 6 ).
Compute (div_ErrorNat (plus_ErrorNat 14 6) (mul_ErrorNat 5 2)).

 
(*                         expresii booleene                          *)

Inductive BExp :=
| berror
| btrue
| bfalse
| bvar: string -> BExp
| blt : AExp -> AExp -> BExp
| bgt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

(*                     notatii operatii booleene                      *)

Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).


(*                 functii de calcul operatii booleene ce trateaza erori                  *)

Definition lt_ErrorBool (n1 n2 : Errnat) : Errbool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | number v1, number v2 => boolean (Nat.ltb v1 v2)
    end.


Definition gt_ErrorBool (n1 n2 : Errnat) : Errbool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | number v1, number v2 => boolean (Nat.ltb v2 v1)
    end.


Definition not_ErrorBool (n :Errbool) : Errbool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.


Definition and_ErrorBool (n1 n2 : Errbool) : Errbool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.


Definition or_ErrorBool (n1 n2 : Errbool) : Errbool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.


(*                 teste                      *)


Compute or_ErrorBool true false.
Compute and_ErrorBool (lt_ErrorBool 10 12) (gt_ErrorBool 2 4).















 
