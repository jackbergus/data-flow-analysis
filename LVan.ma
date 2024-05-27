(**************************************************************************)
(* Giacomo Bergami (c) 2014                                               *)
(**************************************************************************)

include "dataflow/VBEan.ma".

definition killLV ≝ λS:stm.λl. 
  match get_lth S l with
    [ aassign n var val ⇒ [var]
    | _ ⇒ []].

definition genLV ≝ λS:stm.λl.
  match get_lth S l with
    [ aassign n x a ⇒ FVe a
    | abval x y ⇒ FVb y
    | _ ⇒ [ ]].

definition LV ≝ λS. mk_framework false false (ℕ) (FV (stmc S)) eqb killLV  genLV true S .


definition LV_bot ≝ λS. make_bot (ℕ) S.
definition LV_step ≝ λs,state. F_step ? s state LV.
definition approx_LV ≝ λn,soft. approx_F ? LV_bot n soft LV.

(*
definition profe_2 ≝ aX <- Nat 2 \jj(
                     aY <- Nat 4 \jj(
                     aX <- Nat 1 \jj((
                     se (vY ≥ vX) allora aZ <- vY altri aZ <- (vY * vY)) \jj(
                     aX <- vZ
                     )))).

example labels_TestLV: (stmc profe_2 )=?. normalize // qed.
example flow_TestLV: flow profe_2=?.  normalize // qed.

example lvt: approx_LV 8 profe_2 =?. normalize // qed.
*)
