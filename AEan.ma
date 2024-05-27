(**************************************************************************)
(* Giacomo Bergami (c) 2014                                               *)
(**************************************************************************)

include "dataflow/framework.ma".


(*
definition software2 ≝ (aX <- (vX + vA) \jj 
              (While ((vX + vA) ≥ ((Nat 2) * vA)) do 
                  (aA <- vX - (Nat 1) \jj (aX <- vX + vA \jj (aB <- (Nat 2) * vA) )) 
              done)).
definition software ≝ (aX <- (vX + vA) \jj 
              (While ((vX + vA) ≥ ((Nat 2) * vA)) do 
                  (aA <- vA + (Nat 1) \jj (aX <- vX + vA \jj (aB <- (Nat 2) * vA) )) 
              done)).
              *)
(*
example blocks_Test: (blocks software)=?. normalize // qed.
example labels_Test: (stmc software)=?. normalize // qed.
example flow_Test: flow software=?.  normalize // qed.
*)

(* Definizione del Monotonicity Framework per le Available Expressions *)
definition killAE ≝ λS:stm.λl. 
  match get_lth S l with
    [ aassign n var val ⇒ filter ? (λy. memf  ? eqb (FVe y) var) (AExp∗(stmc  S)) 
    | _ ⇒ []].

definition genAE ≝ λS:stm.λl.
  match get_lth S l with
    [ aassign n x a ⇒ filter ? (λy. (notb (memf ? eqb (FVe y) x))) (AExp_a a)
    | abval l b ⇒ AExp_b b 
    | _ ⇒ [ ]].

definition AE_top ≝ λS. make_list ? 〈AExp∗(stmc S),AExp∗(stmc S)〉 ((length ? (blocks S))-1).
  

definition AE ≝ λS. mk_framework true true expr [] expr_e killAE  genAE false S .
(* example AEval: AE=?. normalize // qed. *)

definition AE_step ≝ λs,state. F_step ? s state AE.
definition approx_AE ≝ λn,soft. approx_F ? AE_top n soft AE.

(* Definizione del Top dal quale far partire la computazione *)

              
(*  
definition AE_step2 ≝ λs,state. state_update ? s state (AE s).
(* Computazione in un numero di passi pari a *)
let rec compute_soft_AE paces soft ≝ 
  match paces with
  [ O ⇒ (AE_top soft)
  | S x ⇒ AE_step soft (compute_soft_AE x soft)].

(* Visualizzazione dei primi “n” passi di computazione *)
definition approx_AE2 ≝ λn,soft.
  map ?? (λn. compute_soft_AE n soft) (make_len_n n).
*)



