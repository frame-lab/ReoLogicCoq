Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.


Set Implicit Arguments.
Set Maximal Implicit Insertion.

Close Scope Q_scope.

(* Utils *)

Program Fixpoint s1_in_s2 {A} `{EqDec A eq} (s1 s2 : set A) :=
  match s1 with
    | [] => true
    | a::t => set_mem equiv_dec a s2 && s1_in_s2 t s2
  end.

(* Calculates whether a set s is a subset of s2 *)

(*Fixpoint subset {A} `{EqDec A eq} (s: set A) (s2 : set (set A)) :=
  match s2 with
  | [] => s1_in_s2 s []
  | a::t => s1_in_s2 s a || subset s t
  end.  *)

Instance option_eqdec A `{EqDec A eq} : EqDec (option A) eq :=
{
  equiv_dec x y :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.
Proof.
all:congruence.
Qed.

Fixpoint set_eq {A} `{EqDec A eq} (s1 s2 : set A) :=
  if (length s1 == length s2) then
      if (s1_in_s2 s1 s2) then
          if (s1_in_s2 s2 s1) then true else false
      else false
  else false.

Lemma set_eq_sound {A} `{EqDec A eq} : forall s1 : set A, forall s2 : set A,
   set_eq s1 s2 = true <-> ((length s1 = length s2))
   /\ s1_in_s2 s1 s2 = true /\ s1_in_s2 s2 s1 = true.
  Proof.
  split.
  - intros. destruct s1. destruct s2.
  + split. reflexivity. split. assumption. assumption.
  + inversion H0.
  + unfold set_eq in H0. destruct equiv_dec in H0.
    case_eq (s1_in_s2 (a :: s1) s2). case_eq (s1_in_s2 s2 (a :: s1)). intros. rewrite H1 in H0. rewrite H2 in H0. inversion e.
    split. reflexivity. auto. intros. rewrite H2 in H0. rewrite H1 in H0. inversion H0. intros. 
    rewrite H1 in H0. inversion H0. congruence. 
  - intros. destruct s1. destruct s2.
  + reflexivity.
  + destruct H0. inversion H0.
  + simpl. destruct H0. destruct H1. simpl in H0. rewrite H0.
    simpl s1_in_s2 in H1. rewrite H1. rewrite H2. repeat simpl. destruct equiv_dec. reflexivity. congruence.
  Defined.

Instance set_eqdec {A} `(eqa : EqDec A eq) : EqDec (set A) eq :=
  { equiv_dec :=
    fix rec (x y : set A) :=
    match x, y with
      | nil, nil => in_left
      | cons hd tl, cons hd' tl' =>
        if hd == hd' then
          if rec tl tl' then in_left else in_right
          else in_right
      | _, _ => in_right
    end }.
Proof.
all:congruence.
Defined.


Module ReoLogicCoq.
  Section ReoLogicCoq.

  Variable name state data: Type.
  Context `{EqDec name eq} `{EqDec data eq}.

  Inductive connector :=
  | sync : name -> name -> connector
  | lossySync : name -> name -> connector
  | fifo : name -> name -> connector
  | syncDrain : name -> name -> connector
  | asyncDrain : name -> name -> connector
  | merger : name -> name -> name -> connector
  | replicator : name -> name -> name -> connector. (*composite operation. Stands for \odot from the logic's language *)
(*   | composite : connector -> connector -> connector. (*isso aqui me da uma espêcie de "árvore". Pode complicar a noção  *)
                                                       de processamento sequencial que a gente ve em g*)

  Open Scope Q_scope.
  (*Frame definition *)
  Record frame := mkframe {
    S : set state;
    R : set (state * state);
    lambda : state -> name -> QArith_base.Q;
    delta : state -> set name
  }.

  Close Scope Q_scope.

  (* Model definition *)
  Record model := mkmodel {
    Fr  : frame;
    V : state -> set Prop (*Erick: em um primeiro momento, prop. Mas imagino que tenhamos
                          um tipo indutivo que define nossa linguagem*)
  }.

  (* Parsing of a Reo program \pi *)

  (* We define an inductive type for the conversion of a reo Connector to a Reo
     program by means of the g function *)


  Inductive program :=
    (*| empty : program -> 15/12 - faz sentido ter empty? digo, considerando o progrmaa como set program e nao como program,
        pra mim não faz sentido *)
    | to : name -> name -> program (* sync *)
    | asyncTo : name -> name -> program (* LossySync : v0 era name ->  name -> name. não vejo necessidade disso *)
    | fifoAlt : name -> name -> program (* fifo *)
    | SBlock : name -> name -> program (* syncDrain *)
    | ABlock : name -> name -> program.  (* asyncDrain *)
    (*| mer : name -> name -> name -> program (* merger *)
    | rep : name -> name -> name -> program. (* replicator *) me parecem desnecessários.*)

  Instance program_eqdec `{EqDec name eq} : EqDec program eq :=
  { equiv_dec x y :=
    match x, y with
      | to a b, to c d  | asyncTo a b, asyncTo c d  | fifoAlt a b, fifoAlt c d 
      | SBlock a b, SBlock c d  | ABlock a b, ABlock c d => 
        if a == c then 
          if b == d then in_left 
          else in_right
        else in_right
      | _, _ => in_right
    end
    }.
  Proof.
  all:congruence.
  Defined.
  (* We define the function which coordinates the flow on the Reo program *)

  Fixpoint g (pi: list connector) (s : list program) : list program := (*alternativamente : set program sem o construtor composite *)
    match pi with
    | [] => s
    | a::t => match a with
              | sync a b => (g(t) (s ++ [to a b]))
              | lossySync a b => (g(t) (s ++ [asyncTo a b]))
              | fifo a b => (g t s) ++ [fifoAlt a b]
              | syncDrain a b => (g(t) ([(SBlock a b)] ++ s))
              | asyncDrain a b => (g(t) [(ABlock a b)] ++ s)
              | merger a b c => (g(t) (s ++ [(to a c); (to b c)])) (* s ++ [(mer a b c)] *)
              | replicator a b c => (g(t) (s ++ [(to a b); (to a c)])) (*s ++ [(rep a b c)]*)
              end
    end.

  (* We define a type which denotes the ports to fire and their respective data *)
  Inductive goMarks :=
    | goTo : name -> name -> goMarks
    | goFifo : name -> data -> name -> goMarks  (*entra no fifo: axb*)
    | goFromFifo : name -> data -> name -> goMarks. (*sai do fifo : axb->b --- preciso guardar essas referências?*) 

  (* We define an inductive type for the data that effectively denote the flow of a 
   circuit: either there are data items on some port names or a data item within a
   buffer *)
  Inductive dataConnector :=
    | fifoData : name -> data -> name -> dataConnector
    | dataPorts : name -> data -> dataConnector.

  Instance dataConnector_eqdec `{EqDec name eq} `{EqDec data eq} : EqDec dataConnector eq :=
  {
  equiv_dec x y :=
    match x, y with
      | dataPorts a b, dataPorts c d => if a == c then 
                                          if b == d then in_left 
                                          else in_right
                                        else in_right
      | fifoData a b c, fifoData d e f => if a == d then 
                                            if b == e then 
                                              if c == f then in_left 
                                              else in_right
                                            else in_right
                                      else in_right
      | _, _ => in_right
    end
    }.
  Proof.
  all:congruence.
  Defined.

  Fixpoint dInSetDataConnector (data: dataConnector) (s: set dataConnector) :=
    match s with 
    | [] => false
    | a::t => if data == a then true else dInSetDataConnector data t
    end.

  Fixpoint subset (s: set dataConnector) (s2 : (set dataConnector)) :=
    match s with
    | [] => true
    | a::t => dInSetDataConnector a s2 && subset t s2
    end.


  (* Auxiliary function for goTo a b and dataPorts a x -> dataPorts b x *)
 Fixpoint port2port (dataSink : goMarks) (dataSource : set dataConnector) :=
  match dataSource with
  | [] => []
  | ax::acc => match ax,dataSink with
               | dataPorts a x, goTo y b => if equiv_decb a y then [dataPorts b x] else port2port dataSink acc
               | _, _ => port2port dataSink acc
                end
  end.


 Fixpoint fire (t: set dataConnector) (s : set goMarks) : set dataConnector :=
    match s with
    | [] => []
    | ax::l => match ax with
              | goTo a b => if (existsb (fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then 
              (*busco o item de dado em t e transformo pro formato adequado*)
                                        (port2port (goTo a b)(filter(fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false 
                                        end) (t)))++(fire t l) else fire t l

              | goFifo a x b => if (existsb (fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then (fifoData a x b)::(fire t l) else fire t l
              | goFromFifo a x b => if (existsb (fun x : (dataConnector) => match x with
                                        | fifoData name1 data name2 => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then (dataPorts b x)::(fire t l) else fire t l
              end
   end. 

  (* Auxiliary definition which removes a data marking from the accumulator which has the same sink port name of
    the data marking which is being currently evaluated*)
  Fixpoint swap (s: set goMarks) (current: goMarks) : set goMarks :=
    match s with
    | [] => []
    | dataMark::t => match dataMark with
                     | goTo a b => match current with (* vou acabar redefinindo isso como outra função *)
                                   | goTo u v => if (equiv_decb b v) then (goTo u v)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                   | goFifo u w v => if (equiv_decb b v) then (goFifo u w v)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                   | goFromFifo u w v => if (equiv_decb b v) then (goFromFifo u w v)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                    end
                     | goFifo a x b => match current with
                                       | goTo x y => if (equiv_decb b y) then (goTo x y)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                       | goFifo x y z => if (equiv_decb b z) then (goFifo x y z)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                       | goFromFifo x y z => if (equiv_decb b z) then (goFromFifo x y z)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                        end
                     | goFromFifo a x b => match current with
                                       | goTo x y => if (equiv_decb b y) then (goTo x y)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                       | goFifo x y z => if (equiv_decb b z) then (goFifo x y z)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                       | goFromFifo x y z => if (equiv_decb b z) then (goFromFifo x y z)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                        end
                     end
    end.

  (* Auxiliary definition to retrieve data from the input t to references of data (i.e., goMarks) for fifos*)

  Fixpoint dataConnectorToGoMarksFifo (t : set dataConnector) : set goMarks :=
    match t with
    | [] => []
    | ax::ta => match ax with
                | fifoData a x b => [goFromFifo a x b]
                | _ => dataConnectorToGoMarksFifo ta
                end
    end.

  (* Auxiliary definition to retrieve data from the input t to references of single data *)
  Fixpoint dataConnectorToGoMarksPorts (t : set dataConnector) (pi: program) : set goMarks :=
    match pi with
    | fifoAlt a b =>  match t with
                  | [] => []
                  | ax::ta => match ax with
                              | dataPorts a x  => [goFifo a x b]
                              | _ => dataConnectorToGoMarksPorts ta pi
                              end
                  end
    | _ => []
    end.

  (*Auxiliary definition to process blocks in the program currently being evaluated. Intuitively, halt removes any further processing *)
  (* of Reo subprograms which have only one source node and this node is somehow a source node directly connected to the (a)syncDrain *)
  (* which condition has failed                                                                                                       *)

  (* halt'' filters programs that has its sink node the port name given as parameter  *)
  Definition halt'' (a: name)  (s': set program) :=
  (filter (fun x : (program) => match x with 
                                        | to name1 name2 => (equiv_decb name1 a)
                                        | asyncTo name1 name2 => (equiv_decb name1 a)
                                        | fifoAlt name1 name2 => (equiv_decb name1 a)
                                        | SBlock name1 name2 => (equiv_decb name1 a)
                                        | ABlock name1 name2 => (equiv_decb name1 a)
                                        end) (s')).

  (* s': programa a ser iterado *)
  (* s'' : próximos programas a serem removidos *)
  Fixpoint halt' (a : name) (s' : set program) (s'': set program) :=
    match (s'') with
    | [] => s'
    | ax::st => set_remove equiv_dec (ax) (s')++halt' a s' st
    end.

  Definition haltAux' (a b : name) (s' : set program) :=
    halt' a s' (halt'' a s') ++ halt' b s' (halt'' b s').

  Fixpoint haltAux (a b: name) (s' : set program) (k: nat) : set program := 
    match k with
    | 0 => haltAux' a b s'
    | Datatypes.S n => haltAux' a b s'
    (* TODO redefinir isso como um fix e iterar, modificando as portas passadas para *)
    (* haltAux' *)
    end.

  Definition halt (a b: name) (s': set program) := haltAux a b s' (length s').

  Fixpoint go (t : set dataConnector) (s: set program) (k: nat) (acc : set goMarks) : set dataConnector := 
    (*obs1: a manipulação de s no caso dos blocks vai dar problema 
    (coq não permite a manipulação do argumento decrescente em definições fix)
    ideia: iterar sobre o tamanho de s*)
    (*obs2: não estou checando se, por exemplo, (a -> b) \nsucc s). Deixarei isso a cargo de g
     Ou seja, acc fica livre de repetição por construção.*)
    (* obs3: a expressividade de casos axb não permite t ser set (name * data). t deve ter tipo set dataConnector *)
    match k with
    | 0 => fire t acc
    | Datatypes.S n => match s with
             | [] => []
             | prog::s' => match prog with
                        | to a b => if existsb (fun x : (dataConnector) => match x with (*a sync b *)
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)then (*condição seguinte verifica se ja tem alguem com o mesmo sink no acc *)
                                          if negb((existsb (fun x : goMarks => match x with
                                            | goTo name1 name2 => (equiv_decb name2 b) 
                                            | goFifo name1 data name2 => (equiv_decb name2 b)
                                            | goFromFifo name1 data name2 => (equiv_decb name2 b)
                                            end) (acc)))
                                         then  (*caso 1*)
                                            (go t s' n (acc++[goTo a b]))
                                         else  (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                            go t s' n ((swap acc (goTo a b))++[goTo a b]) ++ (go t s' n (acc))
                                      else 
                                      (go t s' n acc)
                         | asyncTo a b => if (existsb (fun x : (dataConnector) => match x with (*a lossySync b *)
                                        | dataPorts name1 name2 => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then (*condição seguinte verifica se ja tem alguem com o mesmo sink no acc *)
                                          if negb((existsb (fun x : goMarks => match x with
                                            | goTo name1 name2 => (equiv_decb name2 b) 
                                            | goFifo name1 data name2 => (equiv_decb name2 b)
                                            | goFromFifo name1 data name2 => (equiv_decb name2 b)
                                            end) (acc))) 
                                          then (*caso 1*)
                                            (go t s' n (acc++[goTo a b])) ++ (go t s' n (acc++[goTo a a]))
                                         else (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                            (go t s' n ((swap acc (goTo a b))++[goTo a b])) ++ (go t s' n (acc))
                                      else 
                                      (go t s' n acc)
                        | fifoAlt a b => if (existsb (fun x : (dataConnector) => match x with (*a fifo b *)
                                        | fifoData name1 data name2 => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then (*condição seguinte verifica se ja tem alguem com o mesmo sink no acc *)
                                          if negb((existsb (fun x : goMarks => match x with
                                            | goTo name1 name2 => (equiv_decb name2 b) 
                                            | goFifo name1 data name2 => (equiv_decb name2 b)
                                            | goFromFifo name1 data name2 => (equiv_decb name2 b)
                                            end) (acc))) 
                                          then (*caso 3 - existe alguem com o mesmo sink*)
                                            (go t s' n (acc++dataConnectorToGoMarksFifo(t))) ++ (go t s' n (acc))
                                         else (*caso 2 - sem portas com mesmo sink em acc mas com axb em t *)
                                            (go t s' n (acc++dataConnectorToGoMarksFifo(t)))
                                      else
                                      if (existsb (fun x : (dataConnector) => match x with  (* caso 1 *)
                                        | fifoData name1 data name2 => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then
                                        (go t s' n (acc++(dataConnectorToGoMarksPorts t (fifoAlt a b)))) (* caso 1 *)
                                      else
                                      (go t s' n acc) 
                        | SBlock a b => if (existsb (fun x : (dataConnector) => match x with (* ax \succ t *)
                                          | dataPorts name1 data => (equiv_decb name1 a)
                                          | _ => false
                                          end) t) && (existsb (fun x : (dataConnector) => match x with (* bx \succ t *)
                                          | dataPorts name1 data => (equiv_decb name1 b) 
                                          | _ => false
                                          end) t) ||
                                          negb((existsb (fun x : (dataConnector) => match x with 
                                          | dataPorts name1 data => (equiv_decb name1 a)
                                          | _ => false
                                          end) t)) && negb(existsb (fun x : (dataConnector) => match x with 
                                          | dataPorts name1 data => (equiv_decb name1 b) 
                                          | _ => false
                                          end) t) then (*caso 1 : existe dataItem p a e p b ou pra ningúem*)
                                            (go t s' n acc)
                                          else
                                            (go t (halt a b s') n acc)
                        | ABlock a b => if (existsb (fun x : (dataConnector) => match x with (* ax \succ t *)
                                          | dataPorts name1 data => (equiv_decb name1 a)
                                          | _ => false
                                          end) t) && (existsb (fun x : (dataConnector) => match x with (* bx \succ t *)
                                          | dataPorts name1 data => (equiv_decb name1 b) 
                                          | _ => false
                                          end) t) ||
                                          negb((existsb (fun x : (dataConnector) => match x with 
                                          | dataPorts name1 data => (equiv_decb name1 a)
                                          | _ => false
                                          end) t)) && negb(existsb (fun x : (dataConnector) => match x with 
                                          | dataPorts name1 data => (equiv_decb name1 b) 
                                          | _ => false
                                          end) t) then (*caso 1 : existe dataItem p a e p b ou pra ningúem*)
                                            (go t s' n acc)
                                          else
                                            (go t (halt a b s') n acc)
                         end
            end
    end.
  
  (* We define f as the top-level function to be used as follows *)
  Definition f (t: set dataConnector) (pi: set connector) : set dataConnector := go t (g pi []) (length pi) [].

  (* We define the computation of iterations bounded by repetition as follows. *)

  Definition boundedIteration : set dataConnector ->  set connector -> nat -> (*set dataConnector -> *)
    set (set dataConnector) -> set (set dataConnector)  :=
    fix rec t pi iterations (*acc*) resp :=
      match iterations with
      | 0 => [last resp t]
      | Datatypes.S n => if existsb (subset t) resp
                         then ([last resp t]) 
                         else (rec (f t pi) pi n (resp ++ [t]))
                          (*set_add equiv_dec t resp)*)
      end.

  End ReoLogicCoq.
End ReoLogicCoq.

Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
