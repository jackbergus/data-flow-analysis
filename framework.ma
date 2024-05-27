(**************************************************************************)
(* Giacomo Bergami (c) 2014                                               *)
(**************************************************************************)

include "dataflow/dataflow.ma".




let rec AExpA s ≝  match s with
[ iassign n a b ⇒ (AExp_a b)
| idskip n ⇒ [ ]
| iconcat a b ⇒ union expr expr_e (AExpA a) (AExpA b)
| iifte n a b c ⇒ union expr expr_e (AExpA b) (AExpA c)
| iwhile n a b ⇒ (AExpA b)].

let rec AExpB s ≝  match s with
[ iassign n a b ⇒ [ ]
| idskip n ⇒ [ ]
| iconcat a b ⇒ union expr expr_e (AExpB a) (AExpB b)
| iifte n a b c ⇒ union expr expr_e (AExp_b a) (union expr expr_e (AExpB b) (AExpB c))
| iwhile n a b ⇒ union expr expr_e (AExp_b a) (AExpB b)].

(*
  Fissato un programma S∗, Lab∗ è l'insieme Labels(S∗)
                           Var∗ è l'insieme delle FV(S∗)
                           AExp∗ è l'insieme delle espressioni con operatore in S∗
                           In particolare AExpA⊆AExp∗ delle espressioni aritmetiche,
                           mentre AExpB⊆AExp∗ delle espressioni booleane.
                           
                           Osserva: AExp∗=AExpA (S) ∪AExpB .

*)


notation "'Lab'∗(a)"  non associative with precedence 90 for @{ labels $a }.
notation "'VarS'∗(a)"  non associative with precedence 90 for @{ FV $a }.
notation "'AExp'∗(a)"  non associative with precedence 90 for @{ AExp $a }.

definition init_entry_exit ≝ λA. 〈nil A, nil A〉.
definition entry  ≝ λA,g. fst (list A) (list A) g.
definition exit  ≝ λA,g. snd (list A) (list A) g.

definition make_bot ≝ λA,s. make_list ? (init_entry_exit A) (length ? (blocks s)). 

(*
definition preceed_flow ≝ λflow:(stm→list (ℕ×ℕ)).λs,l. 
    map ?? (λx. fst ?? x) (filter ? (λx. eqb (snd ?? x) l) (flow s)).
*)  
definition preceed_flows ≝ λs,l. 
    map ?? (λx. fst ?? x) (filter (ℕ×ℕ) (λx. eqb (snd ?? x) l) s).

(*
definition preceed_fflow ≝ λflow:(idxstm→list (ℕ×ℕ)).λs,l. 
    map ?? (λx. fst ?? x) (filter ? (λx. eqb (snd ?? x) l) (fflow s)).
*)

(* Mi estrae l'n-esimo elemento della lista, ed effettua la proiezione della coppia contenuta *)
definition nth_list_proj ≝ λA. λn. λproj: (∀A: Type[0] .(list A)×(list A)→list A). λll: list ((list A)×(list A)). 
  match (nth_opt ? n ll) with
  [ None ⇒ [ ]
  | Some a ⇒ proj A a].

(*
definition killAE2 ≝ λS,l. 
  match (get_lth S l) with
    [ aassign n var val ⇒ filter ? (λy. memf  ? eqb (FVe y) var) (AExp∗(stmc S)) 
    | _ ⇒ []].*)
definition KillGenType ≝ stm→ℕ→list expr.



(* Aggiorna una posizione l-esima, che può essere entry o exit in base al paradigma 
   (Restituisce quindi una (list A)*)
definition group_of_l ≝ 
    λA.                               (* Valore restituito: Tipo *)
    λE:list nat.                      (* Lista delle etichette degli elementi iniziali *)
    λi:list A.                        (* Inizializzazioni dei nodi base *)
    λF:list (ℕ×ℕ).                    (* Definizione della lista di flusso *)
    λeq:A→A→bool.                     (* Funzione di equivalenza sugli A *)
    λSup:(∀A: Type[0].(A→A→bool)→list (list A)→list A). (* Funzione di ⊔ *)
    λproj:(∀A: Type[0] .(list A)×(list A)→list A). (* Funzione di proiezione *)
    λkill,gen:  stm→ℕ→list A.
    λinit:bool. (* richiedo se vuole il valore di inizializzazione *)
    λS:stm.
    λl:ℕ. 
    λiter:list ((list A)×(list A)).   (* Passo precedente di iterazione *)
  
  if (andb (memf ℕ eqb E l) init) then 
    ((Sup A eq (i::(map ?? (λx. nth_list_proj ? x proj iter) (preceed_flows F l))) )) 
  else 
    (Sup A eq (map ?? (λx. nth_list_proj ? x proj iter) (preceed_flows F l)) ).


definition from_of_l ≝
    λA.                               (* Valore restituito: Tipo *)
    λE:list nat.                      (* Lista delle etichette degli elementi iniziali *)
    λi:list A.                        (* Inizializzazioni dei nodi base *)
    λF:list (ℕ×ℕ).                    (* Definizione della lista di flusso *)
    λeq:A→A→bool.                     (* Funzione di equivalenza sugli A *)
    λSup:(∀A: Type[0].(A→A→bool)→list (list A)→list A). (* Funzione di ⊔ *)
    λproj:(∀A: Type[0] .(list A)×(list A)→list A). (* Funzione di proiezione *)
    λkill,gen:  stm→ℕ→list A.
    λinit:bool. (* richiedo se vuole il valore di inizializzazione *)
    λS:stm.
    λl:ℕ. 
    λiter:list ((list A)×(list A)).   (* Passo precedente di iterazione *)

    union A eq (difference A eq (group_of_l A E i F eq Sup proj kill gen init S l iter) (kill S l)) (gen S l).


(*
example ex: blocks  (((5<- Nat 2); (6 <- Nat 3); While ⊤ do 6<- Nat 3 done))=?.
normalize
*)


record MonotonicFramework (A : Type[0]) : Type[1] ≝ {
    E : list nat;   (* Lista delle etichette d'entrata o uscita *)
    i : list A;     (* Inizializzazione dei valori base *)
    F : list (ℕ×ℕ); (* Definizione del flusso *)
    eq: A→A→bool;   (* Funzione di equivalenze su A *)
    Sup:(∀A: Type[0].(A→A→bool)→list (list A)→list A); (* Funzione di superiore *)
    proj:(∀A: Type[0] .(list A)×(list A)→list A);      (* Funzione di proiezione *)
    kill:(stm→ℕ→list A);                   (* Funzione di eliminazione *)
    gen:(stm→ℕ→list A);                    (* Funzione di generazione *)
    init:bool;                             (* richiedo se vuole il valore di 
                                              inizializzazione *)
    Fforw:bool;                             (* Richiedo come debba essere fatto il forward *)
    MFentry: stm→ℕ→list ((list A)×(list A))→list A;
    MFexit: stm→ℕ→list ((list A)×(list A))→list A
}.

(* Definisce il verso d'analisi del flusso *)
definition F_isForw ≝ λb. if b then flow else fflowR.

(* Definisce da quali stati far partire l'analisi, in base alla direzione del flusso *)
definition E_isForw ≝ λb,g. if b then [init g] else final g.

(* Definisce il tipo di operatore, in base a may/must *)
definition Sup_isMust ≝ λb. if b then Intersect else Union.

(* Proiezione delle entry *)
definition projEn_isForw ≝ λb. if b then exit else entry.

(* Proiezione delle exit (inverso della precedente) *)
definition projEx_isForw ≝ λb.  projEn_isForw (notb b).

(* Scelta della funzione da operare sulla quale operare *)
(* XXX
definition entry_isForw ≝ λb. if b then group_of_l else from_of_l.
definition exit_isForw ≝ λb. entry_isForw (notb b).
*)
definition entry_isForw ≝ group_of_l.
definition exit_isForw ≝ from_of_l.

definition eiF ≝ λforw, A, program, i, eq, must, ini. λkill:?. λ gen. 
entry_isForw A (E_isForw forw program) i (F_isForw forw program) eq 
             (Sup_isMust must) (projEn_isForw forw) kill gen ini.
definition xiF ≝ λforw, A, program, i, eq, must, ini. λkill:?. λ gen. 
exit_isForw A (E_isForw forw program) i (F_isForw forw program) eq 
             (Sup_isMust must) (projEn_isForw forw) kill gen ini.           

definition mk_framework ≝ 
      (λforw,must.
       λA,i,eq,kill,gen,init.
       λprogram.
         mk_MonotonicFramework A 
                               (E_isForw forw program)
                               i
                               (F_isForw forw program)
                               eq
                               (Sup_isMust must)
                               (projEn_isForw forw)
                               kill
                               gen
                               init
                               forw
                               (eiF forw A program i eq must init kill gen )
                               (xiF forw A program i eq must init kill gen )
      ).

(* Definisce l'aggiornamento della posizione l-esima nella lista *)
definition lth_state_update: ∀A. stm→list ((list A)×(list A))→MonotonicFramework A→ℕ→((list A)×(list A))
≝ λA.λprog. λstate. λfm. λlab. 
  if (Fforw A fm) then
  〈(MFentry A fm prog lab state),(MFexit A fm prog lab state)〉
  else 
  
  〈(MFexit A fm prog lab state),(MFentry A fm prog lab state)〉.

(* Crea una lista di numeri da 0 ad n *)
let rec make_len_n n ≝ 
  match n with
  [ O ⇒ [O]
  | S x ⇒ (make_len_n x)@[S x]].

(* Dato una soluzione state, in base alla lunghezza del programma definisce un
   nuovo stato, del quale viene applicato l'aggiornamento in base alle
   regole del framework frame *)
definition state_update ≝ λA.λprog. λstate. λframe.  
map ?? (λx. lth_state_update A prog state frame x) (make_len_n ((length ? (blocks prog))-1)).

(* La funzione di cui sopra fornisce la computazione di un passo *)
definition F_step ≝ λA.λs,state.λF: (stm→MonotonicFramework A). state_update ? s state (F s).

(* Computazione di un elemento in un numero di passi p *)
let rec compute_soft_F A 
                      (start:stm→list ((list A)×(list A))) 
                      p 
                      soft 
                      (F:stm→MonotonicFramework A)
                      on p ≝ 
  match p with
  [ O ⇒ (start soft)
  | S x ⇒ (F_step A soft (compute_soft_F A start x soft F) F)].
  
definition approx_F ≝ λA,start,paces,soft,F.
  map ?? (λn. compute_soft_F A start n soft F) (make_len_n paces).
