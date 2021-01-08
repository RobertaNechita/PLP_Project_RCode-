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

(*        functiile ajutatoare strcat & strlen & strcmp        *)

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
|ERR_string :Value_Result
|DEFAULT : Value_Result
|nat_val : Errnat -> Value_Result
|bool_val : Errbool -> Value_Result
|string_val : string -> Value_Result.



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
|ERR_string => match type2 with
               |ERR_string => true
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
| avar: string -> AExp 
| anum: Errnat -> AExp
| aplus: AExp -> AExp -> AExp
| amin: AExp -> AExp -> AExp
| amul: AExp -> AExp -> AExp 
| adiv: AExp -> AExp -> AExp 
| alength: string -> AExp
| amodulo: AExp -> AExp -> AExp.

Coercion anum: Errnat >-> AExp.
Coercion avar: string >-> AExp.


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

(*      operatii pe string uri -v2                *)

Definition len_ErrorNat (r: Value_Result) : Errnat :=
match r with
 | string_val s => STRLEN s
 | _ =>0
end.

Compute len_ErrorNat (string_val "plp").
Notation "'len' S" := (len_ErrorNat S)(at level 0).
Compute len (string_val "test").

Definition CONCAT (s1 s2 : Value_Result) : Value_Result :=
match s1 ,s2 with
|string_val sir1, string_val sir2 => string_val (STRCAT sir1 sir2)
|_,_=> ERR_string
end.

Compute CONCAT (string_val "test") ( string_val "plp") .
Notation " S +str+ S' " := (CONCAT S S')(at level 0).
Compute (string_val "Proiect") +str+ (string_val "PLP").

(*              statement-uri                   *)
Inductive Stmt :=
| nat_decl: string ->  Stmt  
| bool_decl: string -> Stmt 
| struct_decl : string ->Stmt -> Stmt
| string_decl : string ->Stmt
| nat_assign : string -> AExp -> Stmt 
| bool_assign : string -> BExp -> Stmt 
| string_assign : string -> string ->Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| case : Errnat -> Stmt -> Stmt
| switch_case : AExp -> Stmt -> Stmt. 



(*                     notatii                        *)
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "'iNat' X ::= A" := (nat_decl X A)(at level 90).
Notation "'iBool' X ::= A" := (bool_decl X A)(at level 90).
Notation "'iStr' X " := (string_decl X) (at level 90).
Notation "'Struct' X {' S }" := (struct_decl X S) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'WHILE' (' B ) {' S }" := (while B S) (at level 93).
Notation "'IF' (' B ) 'THEN' {' S } 'ELSE' {' S2 }" := (ifthenelse B S S2) (at level 93).
Notation "'IF' (' B ) 'THEN' {' S }" := (ifthen B S)( at level 93).
Notation "'FOR' ( A ~ B ~ C ) { S }" := (A ;; while B (S ;; C)) (at level 97).
Notation "'Strcpy' (' S1 , S2 )":= (Copy_string S1 S2) (at level 93).   ( *    operatii pe string uri *)
Notation "'Strcat' (' S1 , S2 )":= (Cat_string S1 S2) (at level 93).
Notation "'Case' (' A ) {' S }" := (case A S) (at level 95).
Notation "'Switch' (' A ) : S " := (switch_case A S) ( at level 93).

Compute iStr "a".
Compute Strcat (' "a" , "b").


(*                 stabilire particulara a valorii default in fct de tipul de date            *)


Definition result_default_value (n: nat) : Value_Result :=
match n with
 | 1 => nat_val 0 
 | 2 => bool_val true
 | 3 => string_val "" 
 | _ => DEFAULT
end.

Definition declare_type (s: Stmt) : nat :=
match s with
| nat_decl n => 1
| bool_decl b=> 2
| string_decl s => 3
| _ => 0
end.


(*Declaratia tipului de date struct*)
Definition struct_concat (s1 s2 :string) : string :=
 STRCAT (STRCAT s1 ".") s2.

Compute struct_concat "plp" "Proiect".

Compute (update env (struct_concat "PLP" "project") DEFAULT) "PLP.project".

(*                     implemetare liste                  *)
Inductive ListElem:=
|nil : ListElem
|push:nat->ListElem->ListElem.

Notation "x :: l" := (push x l)(at level 60, right associativity).
Notation " [ ] " := ( nil )(at level 96).   (*lista vida*)
Notation " [ x ; .. ; y ] " := (push x .. (push y nil) ..)(at level 80).
Compute [ 10 ; 12 ; 3 ].
Compute [ ].

Definition head_of_list (l : ListElem) : nat :=
  match l with
  | nil => 0
  | h :: t => h
  end.

Fixpoint length_of_list (l:ListElem) : nat :=
    match l with
      | nil => 0
      | _ :: m => S (length_of_list m)
    end.

Fixpoint concatenate (l1 l2 : ListElem) : ListElem :=
  match l1 with
  | nil => l2
  | h :: t => h :: (concatenate t l2)
  end.

 Fixpoint last_of_list (l:ListElem) : nat :=
  match l with
    | [] => 0
    | [a] => a
    | a :: l => last_of_list l 
  end.
  
  
Fixpoint removelast (l: ListElem) : ListElem :=
    match l with
      | [] => []
      | [a] => []
      | a :: l => a :: removelast l
    end.

(*                  notatii                  *)

Notation " 'len' L " := (length_of_list L)(at level 0).
Notation " L' 'concat' L " := (concatenate L' L)(at level 0).
Notation " 'head' L " := (head_of_list L)(at level 0).
Notation " 'last' L" := (last_of_list L)(at level 0).
Notation " 'removeLAST' L " := (removelast L)(at level 0).


(*                 teste                    *)
Compute len[ 12 ; 3 ].
Compute len[ 13 ; 7 ; 23 ; 4 ].
Compute [ 12 ; 4] concat [ 1 ; 2 ; 4].
Compute head[12 ; 4 ; 6].
Compute last[3 ; 5 ; 32 ; 1 ].
Compute removeLAST[ 4 ; 3 ; 5 ].

(*                        referinte                *)

Inductive Mem := 
| mem_default : Mem
| offset: nat -> Mem. 

Scheme Equality for Mem.

Definition MemEnv := string -> Mem.
Definition MemLayer := Mem -> Value_Result.
Definition Stack := list MemEnv.
Inductive Configuratie :=
|config : nat -> MemEnv -> MemLayer -> Stack -> Configuratie.

(*                     update memorie /daca variabila are asignata zona default de memorie ii se atribuie un offset                  *)
 Definition update_env ( env : MemEnv)(x : string) (n: Mem) : MemEnv :=
fun y =>
        if( andb (string_beq x y) (Mem_beq (env y) mem_default))
        then n
        else (env y).
(*                    intial toate variabilele primesc o zona default de memorie             *)

Definition env_default : MemEnv := fun x => mem_default.

Compute (env_default "x").
Compute (update_env env_default "x" (offset 0)) "x".


Definition update_memLayer (mem : MemLayer) (env : MemEnv) (x : string)( type : Mem)(v :Value_Result) : MemLayer :=
fun y =>
  if(andb (Mem_beq y type ) (Mem_beq (env x) type))
  then 
    if(andb (check_equality_types ERR_undec (mem y)) (negb (check_equality_types DEFAULT v)))
    then ERR_undec
    else if(andb (check_equality_types ERR_undec (mem y)) (check_equality_types DEFAULT v))
    then DEFAULT
    else
        if(orb (check_equality_types DEFAULT (mem y)) (check_equality_types DEFAULT v))
        then ERR_assign
        else v
    else (mem y).

(*   fiecare nume de variabila mapeaza intial catre undec  *)

Definition mem : MemLayer := fun x=> ERR_undec.

Notation " 'ref' A" := ( (update_env env_default A (offset 6)) "a" ) (at level 0).

Compute ref"x".
Compute ref"a".

(*Definition reference (x :string)( env :MemEnv) :MemEnv:=
fun y =>
    if( andb (string_beq x y) (Mem_beq (env y) mem_default))
      then if (  eqb x "a" )
           then offset 1
           else if (  eqb x "b" )
                then offset 2
                else offset 3
      else (env y).
*)


(*                              Semantica                                   *)

(*evaluare expresii aritmetice*)
Fixpoint aeval_fun (a : AExp) (env : Env) : Errnat :=
  match a with
  | avar v => match (env v) with
                | nat_val n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amin a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | alength S1 => len_ErrorNat (env S1)
  | amodulo a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  
  end.
  
(*teste*)
Compute aeval_fun ("var" +' 3) (update (update env "var" (DEFAULT)) "var" (nat_val 17) ).
Compute aeval_fun ( STRLEN ("abcd" ) +' 5 ) env.


(*evaluare expresii booleane*)
Fixpoint beval_fun (a : BExp) (env : Env) : Errbool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match (env v) with
                | bool_val n => n
                | _ => error_bool
                end
  | blt a1 a2 => (lt_ErrorBool (aeval_fun a1 env) (aeval_fun a2 env))
  | bgt a1 a2 => (gt_ErrorBool (aeval_fun a1 env) (aeval_fun a2 env))
  | bnot b1 => (not_ErrorBool (beval_fun b1 env))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 env) (beval_fun b2 env))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 env) (beval_fun b2 env))
  end.


(*evaluare declarare struct*)
Fixpoint struct_is_declared ( env : Env) (s: string) (stm : Stmt) : Env :=
match stm with
 | nat_decl x => update (update env (struct_concat s x) DEFAULT) (struct_concat s x) (nat_val 0)
 | bool_decl x => update (update env (struct_concat s x) DEFAULT) (struct_concat s x) (bool_val true) 
 | string_decl x => update (update env (struct_concat s x) DEFAULT) (struct_concat s x) (string_val "")
 | sequence b c =>if(Nat.ltb 0 (declare_type b))
                  then match b with
                       | nat_decl x => struct_is_declared (update (update env (struct_concat s x) DEFAULT) (struct_concat s x) (nat_val 0) ) s c
                       | bool_decl x => struct_is_declared (update (update env (struct_concat s x) DEFAULT) (struct_concat s x) (bool_val true) ) s c
                       | string_decl x => struct_is_declared (update (update env (struct_concat s x) DEFAULT) (struct_concat s x) (string_val "") ) s c
                       | _ => env
                       end
                  else env
 
 | _ => env
end.


(*test*)
Compute (struct_is_declared env "plp" (  iStr "proj" ) ) "plp.proj".


(*evaluare statement-uri*)
Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                | nat_decl a => update (update env a DEFAULT) a (nat_val 0)
                | bool_decl b => update (update env b DEFAULT) b (bool_val true)
                | string_decl s => update env s DEFAULT 
                | struct_decl s n =>struct_is_declared env s n
                | nat_assign a aexp => update env a (nat_val (aeval_fun aexp env))
                | bool_assign b bexp => update env b (bool_val (beval_fun bexp env))
                | string_assign s word => update env s (string_val word)

                | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas'
                
                | ifthen cond s' => 
                    match (beval_fun cond env) with
                    | error_bool => env
                    | boolean v => match v with
                                 | true => eval_fun s' env gas'
                                 | false => env
                                 end
                    end
                | ifthenelse cond S1 S2 => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v  => match v with
                                 | true => eval_fun S1 env gas'
                                 | false => eval_fun S2 env gas'
                                 end
                         end
                | while cond s' => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v => match v with
                                     | true => eval_fun (s' ;; (while cond s')) env gas'
                                     | false => env
                                     end
                        end
                | case n St =>eval_fun St env gas'
               
                | switch_case ArithExp C =>
                                 match C with
                                         | case n Stm => if(Errnat_beq n (aeval_fun ArithExp env))  
                                                       then eval_fun Stm env gas'
                                                        else env
                                         | sequence S1 S2 => match S1 with    
                                                              | case n Stm => if(Errnat_beq n (aeval_fun ArithExp env))  
                                                                            then eval_fun Stm env gas'   
                                                                            else eval_fun (switch_case ArithExp S2) env gas'
                                                               | _ => env
                                                                end
                                         | _ => env
                                 end
              
                end
    end.


 
 
(*                                teste                                       *)
Definition Switch_verif :=
 iNat "num1" ;;
 iNat "num2" ;;
 iStr "msg" ;;
 "msg":s= "Hello_WORLD" ;;
"num1" :n= 7 %' 4 ;;
Switch ('"num1" -' 1 ) : 
Case ('2) {' "num2" :n= 3};;
Case ('6) {' "num2" :n= 8};;
Case ('10) {' "num2" :n= 13}.

Compute (eval_fun Switch_verif env 100) "num".
Compute (eval_fun Switch_verif env 100) "num2".
Compute (eval_fun Switch_verif env 100) "msg".
Compute (eval_fun Switch_verif env 100) "num1".

Definition Struct_verif :=
iStr "Elev" ;;
iStr "s2" ;;
Struct "Elev" {' iNat "nota" ;; iStr "curs" }.

Compute (eval_fun Struct_verif env 100 ) "Elev.curs".
Compute (eval_fun Struct_verif env 100 ) "Elev.nota".

Definition prg_test1 :=
iNat "num";;
iBool "verif";;
"verif" :b= btrue;;
 "num" :n=12 ;;
 IF ('"num" >' 7 ) THEN {' "num" :n= 3 ;; "verif" :b= bfalse  }.

Compute (eval_fun prg_test1 env 100) "num".
Compute (eval_fun prg_test1 env 100) "verif".
