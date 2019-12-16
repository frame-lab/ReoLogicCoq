Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.


Set Implicit Arguments.
Set Maximal Implicit Insertion.

Module ReoLogicCoq.
  Section ReoLogicCoq.

  Variable name state data: Type.
  Context `{EqDec name eq}.

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
Check sync.

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
    f  : frame;
    v : state -> set Prop (*Erick: em um primeiro momento, prop. Mas imagino que tenhamos
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


  Eval compute in (existsb (fun x : (name * data) => match x with
                                        | (x,y) => true
                                        end)).


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

  Fixpoint halt (a b : name) (s' : set program) := s'.

  Close Scope Q_scope.

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
  
  End ReoLogicCoq.
End ReoLogicCoq.

Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
