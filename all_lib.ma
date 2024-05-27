(**************************************************************************)
(* Giacomo Bergami (c) 2014                                               *)
(**************************************************************************)
include "dataflow/CPan.ma".

(* Definizioen di alcune costanti d'esempio *)
definition aX ≝ 1.
definition aY ≝ 2.
definition aZ ≝ 3.
definition aA ≝ 4.
definition aB ≝ 5.
definition aN ≝ 6.
definition aM ≝ 7.
definition aR ≝ 8.
definition aS ≝ 9.
definition aT ≝ 10.
definition aU ≝ 11.
definition aV ≝ 11.

definition vX ≝ Var aX.
definition vY ≝ Var aY.
definition vZ ≝ Var aZ.
definition vA ≝ Var aA.
definition vB ≝ Var aB.
definition vN ≝ Var aN.
definition vM ≝ Var aM.
definition vR ≝ Var aR.
definition vS ≝ Var aS.
definition vT ≝ Var aT.
definition vU ≝ Var aU.
definition vV ≝ Var aV.

(*
definition maggio24_2012 ≝ (While (vX) ≥ (vA - vB) do (se (vA ≥ vB) allora (aX <- (vA - vB)* vX) altri (aX <- (vA - vB)* vX)) done).

example blocks_Test: (blocks maggio24_2012)=?. normalize // qed.
example labels_Test: (stmc maggio24_2012)=?. normalize // qed.
example flow_Test: flow maggio24_2012=?.  normalize // qed.

example at: approx_AE 4 maggio24_2012 =?. normalize // qed.
*)


(*

  Ricorda: 
  
   Dato un algoritmo S∗
  
    - (stmc S∗)        ⇒ fornisce l'algoritmo etichettato
    - (flow S∗)        ⇒ fornisce l'insieme del flusso dell'algoritmo
    - (approx_XY 5 S∗) ⇒ fornisce l'approssimazione dell'iterazione XY su S∗


*)

definition e15_giugno_2012 ≝  ( aS <- Nat 1 \jj(
                                           While (vN ≥ Nat 0) do
                                              (se (vN ≥ Nat 0) allora
                                                (aR <- vS + Nat 1 \jj (aN <- vN - Nat 1))
                                               altri
                                                (aR <- vS + Nat 1 \jj (aS <- vR - Nat 1))
                                              )
                                           done)).
(*
example teste15L: stmc e15_giugno_2012 =?. normalize // qed.
example flow15L:  flow e15_giugno_2012 =?. normalize // qed.                                                                                     
example teste15: approx_LV 5  e15_giugno_2012 = ?. normalize // qed.                                 
*)

definition ex_test ≝ (aB <- (vY - vX) \jj (aA <- (vX + vY)) \jj
                         (  (  aX <- (vX + vY) * (vY - vX) ))).

example t_66: approx_VB 4 ex_test =?. normalize

definition ex_6giu11 ≝ (se (vX ≥ vY) allora 
                         (aZ <- vX + vY \jj (aV <- vX -vY))
                        altri
                         (aZ <- vY - vX \jj (aV <- vX + vY))) \jj (  aX <- (vX + vY) * (vY - vX) ).


example t_66: approx_VB 8 ex_6giu11 =?. normalize


definition e5_luglio_2012 ≝ ( aZ <- vX - vY \jj (
                              While (vX ≥ vY) do
                                (( se ( vX - vY ≥ vU) allora
                                    aX <- vX -  vU
                                  altri
                                    aY <- vY - vU )\jj (
                                
                                  aZ <- vX - vY
                                
                                  ))
                              done)).

example t_5lu: stmc e5_luglio_2012 =?. normalize // qed.
example f_5lu: flow e5_luglio_2012 =?. normalize // qed.
example c_5lu: approx_VB 8 e5_luglio_2012 =?. normalize 
