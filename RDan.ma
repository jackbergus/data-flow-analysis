(**************************************************************************)
(* Giacomo Bergami (c) 2014                                               *)
(**************************************************************************)

include "dataflow/AEan.ma".

inductive LabelExt : Type[0] ≝ lnat : nat →LabelExt | wat : LabelExt.

(*
example labels_Test2: (blocks maggio24_2012)=?. normalize // qed.
*)

definition isAAssign  ≝ λlth. match lth with [ aassign _ _ _ ⇒ true | _ ⇒ false ].

definition cp_e ≝ λx,y:Prod ℕ LabelExt.
  match x with
  [ mk_Prod a b ⇒ match y with [ mk_Prod c d ⇒ (andb (eqb a c)
                               (match b with
                                [ lnat u ⇒ match d with [ lnat v ⇒ eqb u v | _ ⇒ false]
                                | wat ⇒ match d with [ wat ⇒ true | _⇒ false]
                                ])) ] ].

definition killRD ≝ λS:stm.λl. 
  match get_lth S l with
    [ aassign n var val ⇒ 〈var,wat〉::(map ?? (λx. 〈var,lnat (get_label_of_asset x)〉) (filter ? isAAssign (blocks S)))
    | _ ⇒ []].

definition genRD ≝ λS:stm.λl.
  match get_lth S l with
    [ aassign n x a ⇒ [〈x,lnat n〉]
    | _ ⇒ [ ]].

definition iRD ≝ λS. map ?? (λx. 〈x,wat〉) (FV (stmc S)).
    
definition RD ≝ λS. mk_framework true false (ℕ×LabelExt) (iRD S) cp_e killRD  genRD true S .

definition RD_bot ≝ λS. make_bot (ℕ×LabelExt) S.
definition RD_step ≝ λs,state. F_step ? s state RD.
definition approx_RD ≝ λn,soft. approx_F ? RD_bot n soft RD.


(*
definition luglio1_2011 ≝ (aX <- Nat 1 \jj 
                          (aY <-  Nat 2 \jj 
                          (aA <- vX) \jj 
                          (While (vB ≥ Nat 2) do 
                                (aA <- vX + vY \jj
                                (aY <- vB \jj
                                (aB <- vB - Nat 1))  
                                ) 
                          done))).

example rt2: approx_RD 8 luglio1_2011 =?. normalize // qed.
*)

(*
definition RD_step ≝ λs,state. state_update ? s state (RD s).

let rec compute_soft start paces soft ≝ 
  match paces with
  [ O ⇒ (start soft)
  | S x ⇒ AE_step soft (compute_soft_AE x soft)].

(* Visualizzazione dei primi “n” passi di computazione *)
definition approx_AE ≝ λn,soft.
  map ?? (λn. compute_soft_AE n soft) (make_len_n n).
  *)
