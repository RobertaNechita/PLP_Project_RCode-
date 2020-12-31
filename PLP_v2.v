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


Compute (update (update env "x" (DEFAULT)) "x" (bool_val true) "x").
















 
