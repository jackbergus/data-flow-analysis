(**************************************************************************)
(* Giacomo Bergami (c) 2014                                               *)
(**************************************************************************)

include "dataflow/RDan.ma".

definition killVB ≝ killAE.

definition genVB ≝ λS:stm.λl.
  match get_lth S l with
    [ aassign n x a ⇒ AExp_a a 
    | abval l b ⇒ AExp_b b 
    | _ ⇒ [ ]].
    
definition VB_top ≝ AE_top.

definition VB ≝ λS. mk_framework false true expr [] expr_e killVB  genVB false S .

definition VB_step ≝ λs,state. F_step ? s state VB.
definition approx_VB ≝ λn,soft. approx_F ? VB_top n soft VB.

(*
definition profe_1 ≝ se (vA ≥ vB) allora 
                          (aZ <- vB - vA \jj
                           (aY <- vA - vB)) 
                    altri (aZ <- vA - vB \jj
                           (aY <- vB - vA )) .

example vbt: approx_VB 4 profe_1 =?. normalize // qed.
*)
