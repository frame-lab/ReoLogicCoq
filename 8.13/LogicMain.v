Require Import ListSet.
Require Import List.
Require Import Classes.EquivDec.
Require Import Coq.Program.Program.
Require Import QArith.
Import ListNotations.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Close Scope Q_scope.


(* Utils *)

Program Fixpoint s1_in_s2 {A} `{EqDec A eq} (s1 s2 : set A) :=
  match s1 with
    | [] => true
    | a::t => set_mem equiv_dec a s2 && s1_in_s2 t s2
  end.

Obligation Tactic := congruence.

Program Instance option_eqdec A `{EqDec A eq} : EqDec (option A) eq :=
{
  equiv_dec (x y: option A) :=
    match x, y with
      | Some a, Some b => if a == b then in_left else in_right
      | None, None => in_left
      | Some _, None | None, Some _ => in_right
    end
 }.

Definition set_eq {A} `{EqDec A eq} (s1 s2 : set A) :=
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
  + unfold set_eq. simpl. destruct H0. destruct H1. simpl in H0. rewrite H0.
    simpl s1_in_s2 in H1. rewrite H1. rewrite H2. repeat simpl. destruct equiv_dec. reflexivity. congruence.
  Defined.

Program Instance set_eqdec {A} `(eqa : EqDec A eq) : EqDec (set A) eq :=
  { equiv_dec :=
    fix rec (x y : set A) :=
    match x, y with
      | nil, nil => in_left
      | cons hd tl, cons hd' tl' =>
        if hd == hd' then
          if rec tl tl' then in_left else in_right
          else in_right
      | nil , cons hd tl | cons hd tl, nil => in_right
    end }.

(*Module ReoLogicCoq.*)
  Section ReoLogicCoq.

  Section LogicMain.

  Variable name state data: Type.
  Context `{EqDec name eq} `{EqDec data eq} `{EqDec state eq}.

  Inductive connector :=
  | sync : name -> name -> connector
  | lossySync : name -> name -> connector
  | fifo : name -> name -> connector
  | syncDrain : name -> name -> connector
  | asyncDrain : name -> name -> connector
  | merger : name -> name -> name -> connector
  | replicator : name -> name -> name -> connector.

Program Instance connectorEqDec {name} `(eqa : EqDec name eq) : EqDec (connector) eq :=
    { equiv_dec :=
      fix rec (x y : connector) :=
      match x,y with
      | sync a b, sync c d => if a == c then if b == d then in_left else in_right else in_right 
      | lossySync a b, lossySync c d => if a == c then if b == d then in_left else in_right else in_right 
      | fifo a b, fifo c d => if a == c then if b == d then in_left else in_right else in_right 
      | syncDrain a b, syncDrain c d => if a == c then if b == d then in_left else in_right else in_right 
      | asyncDrain a b, asyncDrain c d => if a == c then if b == d then in_left else in_right else in_right 
      | merger a b c, merger d e f => if a == d then 
                                        if b == e then 
                                          if c == f then in_left 
                                          else in_right 
                                         else in_right 
                                      else in_right
      | replicator a b c, replicator d e f => if a == d then 
                                                if b == e then 
                                                  if c == f then in_left 
                                                  else in_right 
                                                else in_right 
                                              else in_right
      | sync a b, lossySync c d | sync a b, fifo c d | sync a b, syncDrain c d | sync a b, asyncDrain c d => in_right
      | sync a b, merger c d e | sync a b, replicator c d e => in_right

      | lossySync a b, sync c d | lossySync a b, fifo c d | lossySync a b, syncDrain c d | lossySync a b, asyncDrain c d => in_right
      | lossySync a b, merger c d e | lossySync a b, replicator c d e => in_right

      | fifo a b, sync c d | fifo a b, lossySync c d | fifo a b, syncDrain c d | fifo a b, asyncDrain c d => in_right
      | fifo a b, merger c d e | fifo a b, replicator c d e => in_right

      | syncDrain a b, sync c d | syncDrain a b, lossySync c d | syncDrain a b, fifo c d | syncDrain a b, asyncDrain c d => in_right
      | syncDrain a b, merger c d e | syncDrain a b, replicator c d e  => in_right

      | asyncDrain a b, sync c d | asyncDrain a b, lossySync c d | asyncDrain a b, fifo c d | asyncDrain a b, syncDrain c d => in_right
      | asyncDrain a b, merger c d e | asyncDrain a b, replicator c d e => in_right

      | merger a b c, sync d e | merger a b c, lossySync d e | merger a b c, fifo d e | merger a b c, syncDrain d e => in_right
      | merger a b c, asyncDrain d e  => in_right
      | merger a b c, replicator d e f => in_right

      | replicator a b c, sync d e | replicator a b c, lossySync d e | replicator a b c, fifo d e | replicator a b c, syncDrain d e => in_right
      | replicator a b c, asyncDrain d e => in_right 

      | replicator a b c, merger d e f   => in_right
      end
    }.

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

  Open Scope Q_scope.
  (*Frame definition *)
  Record frame := mkframe {
    S : set state;
    R : set (state * state);
    lambda : state -> name -> QArith_base.Q;
    delta : state -> set dataConnector
  }.

  Close Scope Q_scope.

  (* Model definition *)
  (* Our valuation function depicts a proposition as a natural number, instead of directly using a member of Prop.
     This is due to execution reasons. Its intuitive idea can
     be expressed as "given a state s and a proposition as a natural number n, it will return whether it is valid or
     not in s"*)
  Record model := mkmodel {
    Fr  : frame;
    V : state -> nat -> bool (*As of 16-04, a função de valoração foi trocada p esta assinatura.*)
                              (*Erick : por questões operacionais (i.e., o que exatamente é um pattern em cima de Prop)
                                Acho que devemos criar uma gramática p falar de proposições.*)
                              (*edit: 10/05 - pode ser o caso de ser uma função state -> prop, e o retorno é uma
                                proposição que denota que a proposição é realmente válida num estado. Parece
                                ser a forma padrão de formalizar modelos de Kripke no Coq.*)
                              (*edit: 10/05 - 2 - trocando p nat segundo a ideia explicada no exemplo, baseada
                                em outras implementações de Kripke semantics em Coq.*)
  }.

  Print model.
  Print frame.

  (*06/04 - Redesign of Reo programs as \pi = (f,b) *)

  Inductive flowProgram :=
    | flowSync : name -> name -> flowProgram
    | flowLossySync : name -> name -> flowProgram
    | flowFifo : name -> name -> flowProgram
    | flowMerger : name -> name -> name -> flowProgram
    | flowReplicator : name -> name -> name -> flowProgram.

  Inductive blockProgram :=
    | flowSyncdrain : name -> name -> blockProgram
    | flowaSyncdrain : name -> name -> blockProgram.

  (* Lifting from \pi = (f,b) to \pi *)

  Inductive reoProgram :=
    | reoProg : set flowProgram -> set blockProgram -> reoProgram.

  Definition singleFlow2Reo (flowProg : flowProgram) := 
    match flowProg with
    | flowSync a b => sync a b
    | flowLossySync a b => lossySync a b
    | flowFifo a b => fifo a b
    | flowMerger a b c => merger a b c
    | flowReplicator a b c => replicator a b c
    end.

  Definition singleBlock2Reo (blockProg : blockProgram) :=
    match blockProg with
    | flowSyncdrain a b => syncDrain a b
    | flowaSyncdrain a b => asyncDrain a b
    end.

  Definition flow2Reo (setFlow : set flowProgram) :=
    map (singleFlow2Reo) setFlow.

  Definition block2Reo (setBlock : set blockProgram) :=
    map (singleBlock2Reo) setBlock.

  (* Now we transform the separation of \pi = (f,b) into \pi' for simplicity's sake *)
  Definition program2SimpProgram (prog : reoProgram) : set connector :=
    match prog with
    | reoProg setFlow setBlock => 
      set_union equiv_dec (block2Reo setBlock) (flow2Reo setFlow)
    end.

  (* Parsing of a Reo program \pi *)

  (* We define an inductive type for the conversion of a reo Connector to a Reo
     program by means of *parse* function *)

  Inductive program :=
    | to : name -> name -> program (* sync, replicator, merger *)
    | asyncTo : name -> name -> program (* LossySync : v0 era name ->  name -> name. não vejo necessidade disso *)
    | fifoAlt : name -> name -> program (* fifo *)
    | SBlock : name -> name -> program (* syncDrain *)
    | ABlock : name -> name -> program.  (* asyncDrain *)

  Program Instance program_eqdec `{EqDec name eq} : EqDec program eq :=
  { equiv_dec x y :=
    match x, y with
      | to a b, to c d  | asyncTo a b, asyncTo c d  | fifoAlt a b, fifoAlt c d 
      | SBlock a b, SBlock c d  | ABlock a b, ABlock c d => 
        if a == c then 
          if b == d then in_left 
          else in_right
        else in_right
      | to a b, asyncTo c d  | to a b, fifoAlt c d 
      | to a b, SBlock c d   | to a b, ABlock c d  
      | asyncTo a b, to c d  | asyncTo a b, fifoAlt c d 
      | asyncTo a b, SBlock c d   | asyncTo a b, ABlock c d 
      | fifoAlt a b, asyncTo c d  | fifoAlt a b, to c d 
      | fifoAlt a b, SBlock c d   | fifoAlt a b, ABlock c d 
      | SBlock a b, asyncTo c d  | SBlock a b, to c d 
      | SBlock a b, fifoAlt c d   | SBlock a b, ABlock c d 
      | ABlock a b, asyncTo c d  | ABlock a b, to c d 
      | ABlock a b, fifoAlt c d   | ABlock a b, SBlock c d => in_right
    end
    }.

  (* We define the function which coordinates the flow on the Reo program *)

  Fixpoint parse (pi: list connector) (s : list program) : list program :=
    match pi with
    | [] => s
    | a::t => match a with
              | sync a b => (parse(t) (s ++ [to a b]))
              | lossySync a b => (parse(t) (s ++ [asyncTo a b]))
              | fifo a b => (parse t s) ++ [fifoAlt a b]
              | syncDrain a b => (parse(t) ([(SBlock a b)] ++ s))
              | asyncDrain a b => (parse(t) [(ABlock a b)] ++ s)
              | merger a b c => (parse(t) (s ++ [(to a c); (to b c)])) (* s ++ [(mer a b c)] *)
              | replicator a b c => (parse(t) (s ++ [(to a b); (to a c)])) (*s ++ [(rep a b c)]*)
              end
    end.

  Lemma parseSoundSync: forall pi : list connector, forall s: list program, forall a b,
                    In (sync a b) pi -> In (to a b) (parse pi s).
  Proof.
  (*intros.
  split.*)
  intros. induction pi. destruct s. simpl in H2. inversion H2. inversion H2. 
  simpl. simpl in H2. destruct H2.
  - rewrite H2. Admitted.

  Program Instance dataConnector_eqdec `{EqDec name eq} `{EqDec data eq} : EqDec (dataConnector) eq :=
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
      | dataPorts a b, fifoData c d e=> in_right
      | fifoData c d e, dataPorts a b => in_right
    end
    }.

  Fixpoint dInSetDataConnector (s: set dataConnector) (data: dataConnector) :=
    match s with 
    | [] => false
    | a::t => if data == a then true else dInSetDataConnector t data
    end.

  Lemma dInSetDataConnectorSound : forall data : dataConnector, forall s: set dataConnector,
                                   dInSetDataConnector s data = true <-> (exists d, In d s /\ d = data).
  Proof.
  intros. split.
  - intros. induction s. simpl in H2. inversion H2.
    simpl in H2. destruct equiv_dec in H2. inversion e. exists a. split.
    simpl. auto. reflexivity.
    apply IHs in H2. destruct H2. destruct H2. exists x.
    split. simpl;auto. exact H3.
  - intros. destruct H2. destruct H2. induction s. inversion H2.
    simpl in H2. destruct H2. rewrite <- H2 in H3. rewrite H3. simpl. destruct equiv_dec. reflexivity.
    congruence. apply IHs in H2. simpl. destruct equiv_dec. reflexivity. exact H2.
  Defined.
 
  Fixpoint subset (s: set dataConnector) (s2 : (set dataConnector)) :=
    match s with
    | [] => true
    | a::t => dInSetDataConnector s2 a && subset t s2
    end.

  Lemma subsetSound : forall s s2 : set dataConnector,
    subset s s2 = true <-> ((forallb (dInSetDataConnector s2) (s) = true) \/ s = []).
  Proof.
  intros. split.
  - intros. induction s. right. reflexivity.
  simpl in H2. simpl. left. rewrite andb_lazy_alt in H2. 
  apply andb_true_intro. case_eq (dInSetDataConnector s2 a). intros. rewrite H3 in H2. apply IHs in H2.
  destruct H2. split. reflexivity. auto. split. reflexivity. rewrite H2. simpl. reflexivity.
  intros. rewrite H3 in H2. inversion H2.
  - intros. induction s. reflexivity. destruct H2. simpl. simpl in H2. rewrite andb_lazy_alt in H2.
  apply andb_true_intro. case_eq (dInSetDataConnector s2 a). intros. rewrite H3 in H2.
  destruct H2. destruct IHs. left. reflexivity. auto. intros. rewrite H3 in H2. inversion H2. inversion H2.
  Defined.

  Fixpoint subSubset (s: set (set dataConnector)) (s2 : (set (set dataConnector))) := 
    match s,s2 with
    | a::t,b::y => subset a b && subSubset t y
    | _,_ => true
    end.


  (* Auxiliary function for goTo a b and dataPorts a x -> dataPorts b x *)
  Fixpoint port2port (dataSink : goMarks) (dataSource : set dataConnector) :=
  match dataSource with 
  | [] => None
  | ax::acc => match ax,dataSink with
               | dataPorts a x, goTo y b => if equiv_decb a y then (Some (dataPorts b x)) else port2port dataSink acc
               | _, _ => port2port dataSink acc
                end
  end.

 Fixpoint fire (t: set dataConnector) (s : set goMarks) (acc: set dataConnector) : set (set dataConnector) :=
    match s with
    | [] =>  match acc with
            | [] => []
            | x::y => [acc]
            end
    | ax::l => match ax with
              | goTo a b => if (existsb (fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then 
              (*busco o item de dado em t e transformo pro formato adequado*)
                                            match (port2port (goTo a b)(filter(fun x : (dataConnector) => match x with
                                            | dataPorts name1 data => (equiv_decb name1 a)
                                            | _ => false 
                                            end) (t))) with
                                            | None => (fire t l acc) 
                                            | Some x => (fire t l (x::acc)) 
                                            end
                                        else fire t l acc

              | goFifo a x b => if (existsb (fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then (fire t l ((fifoData a x b)::acc)) else fire t l acc
              | goFromFifo a x b => if (existsb (fun x : (dataConnector) => match x with
                                        | fifoData name1 data name2 => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then (fire t l ((dataPorts b x)::acc)) else fire t l acc
              end
   end. 

  (* Auxiliary definition which removes a data marking from the accumulator which has the same sink port name of
    the data marking which is being currently evaluated*)
  Fixpoint swap (s: set goMarks) (current: goMarks) : set goMarks :=
    match s with
    | [] => []
    | dataMark::t => match dataMark with
                     | goTo a b => match current with (*ERICK: vou acabar redefinindo isso como outra função. TODO verificar *)
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

  Lemma dataConnecetorToGoMarksFifo : forall t : set dataConnector, forall a, forall b, forall x, 
    dataConnectorToGoMarksFifo t = [goFromFifo a x b] -> In (fifoData a x b) t.
  Proof.
  intros. induction t. simpl in H2. inversion H2. simpl in H2. case_eq (a0). intros. rewrite H3 in H2.
  inversion H2. simpl. auto. intros. rewrite H3 in H2.
  inversion H2. simpl. auto. 
  Defined.

  (* Auxiliary definition to retrieve data from the input t to references of single data *)
  Fixpoint dataConnectorToGoMarksPorts (t : set dataConnector) (pi: program) : set goMarks :=
    match pi with
    | fifoAlt a b =>  match t with
                  | [] => []
                  | ax::ta => match ax with
                              | dataPorts c x  => if (a == c) then [goFifo a x b] else dataConnectorToGoMarksPorts ta pi
                              | _ => dataConnectorToGoMarksPorts ta pi
                              end
                  end
    | _ => []
    end.

  (*Auxiliary definition to process blocks in the program currently being evaluated. Intuitively, halt removes any further processing *)
  (* of Reo subprograms which have only one source node and this node is somehow a source node directly connected to the (a)syncDrain *)
  (* which condition has failed                                                                                                       *)

  (* halt'' filters programs that does not have its sink node the port name given as parameter  *)
   Definition halt'' (s': set program) (a: name)  : set program :=
  (filter (fun x : (program) => match x with 
                                        | to name1 name2 => (nequiv_decb name1 a)
                                        | asyncTo name1 name2 => (nequiv_decb name1 a)
                                        | fifoAlt name1 name2 => (nequiv_decb name1 a)
                                        | SBlock name1 name2 => (nequiv_decb name1 a)
                                        | ABlock name1 name2 => (nequiv_decb name1 a)
                                        end) (s')).

  (*Retrieves port names that are on the sink node of a ReLo Program *)
  Fixpoint retrieveNextportNames (s' : set program ) (a : name) : set name :=
    match s' with
    | [] => []
    | program::programs => match program with
                           | to name1 name2 
                           | asyncTo name1 name2
                           | fifoAlt name1 name2 => if name1 == a 
                                                    then (set_add equiv_dec name2 (retrieveNextportNames programs a))
                                                    else (retrieveNextportNames programs a)
                           | _ => retrieveNextportNames programs a
                           end
    end.


  Fixpoint haltAux (names : set name) (acc : set name) (s': set program) (k: nat) : set name :=
    (*s' : original program*) 
    match k with
    | 0 => names
    | Datatypes.S n => haltAux (set_union equiv_dec names (acc)) (flat_map (retrieveNextportNames s') (names)) s' n
    end.

  Fixpoint removePortNames (s: set program) (names : set name) :=
    match names with
    | [] => s
    | a::moreNames => removePortNames (halt'' s a) moreNames
    end.

  (*This definition is used to remove connectors which are attached to a (a)SyncDrain which did not fulfill
    its requirements to fire the channel*)
  Definition halt (names : set name) (s': set program) := 
    removePortNames s' (haltAux names names s' (length s')).

  Fixpoint go (s: set program) (k: nat) (acc : set goMarks) (t : set dataConnector) : set (set dataConnector) := 
    (*obs2: não estou checando se, por exemplo, (a -> b) \nsucc s). Deixarei isso a cargo de parse
     Ou seja, acc fica livre de repetição por construção.*)
    match k with
    | 0 => fire t acc []
    | Datatypes.S n => match s with
             | [] => fire t acc []
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
                                            (go s' n (acc++[goTo a b]) t)
                                         else  (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                             (go s' n (swap acc (goTo a b)) t(*++[goTo a b]*)) ++ (go s' n (acc) t)
                                      else 
                                      (go s' n acc t)
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
                                            (go s' n (acc++[goTo a b]) t) ++ (go s' n (acc++[goTo a a])  t)
                                         else (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                            (go s' n ((swap acc (goTo a b))++[goTo a b]) t) ++ (go s' n (acc) t)
                                      else 
                                      (go s' n acc t)
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
                                            (go s' n (acc++dataConnectorToGoMarksFifo(t)) t) ++ (go s' n (acc) t)
                                         else (*caso 2 - sem portas com mesmo sink em acc mas com axb em t *)
                                            (go s' n (acc++dataConnectorToGoMarksFifo(t)) t)
                                      else
                                      if (existsb (fun x : (dataConnector) => match x with  (* caso 1 *)
                                        | fifoData name1 data name2 => (equiv_decb name1 a)
                                        | dataPorts name1 name2 => (equiv_decb name1 a)
                                        end) (t)) then
                                        (go s' n (acc++(dataConnectorToGoMarksPorts t (fifoAlt a b))) t) (* caso 1 *)
                                      else
                                      (go s' n acc t) 
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
                                            (go s' n acc t)
                                          else
                                            (go (halt [a;b] s') n acc t)
                        | ABlock a b => if negb((existsb (fun x : (dataConnector) => match x with (* ax \succ t *)
                                          | dataPorts name1 data => (equiv_decb name1 a)
                                          | _ => false
                                          end) t)) && negb((existsb (fun x : (dataConnector) => match x with (* bx \succ t *)
                                            | dataPorts name1 data => (equiv_decb name1 b) 
                                            | _ => false
                                            end) t)) || (existsb (fun x : (dataConnector) => match x with (* ax \succ t *)
                                          | dataPorts name1 data => (equiv_decb name1 a)
                                          | _ => false
                                          end) t) && (existsb (fun x : (dataConnector) => match x with (* bx \succ t *)
                                            | dataPorts name1 data => (equiv_decb name1 b) 
                                            | _ => false
                                            end) t)
                                          then  
                                          (*If both ports have data, the aSyncDrain should not fire*)
                                          (go (halt [a;b] s') n acc t)
                                        else
                                          if negb((existsb (fun x : (dataConnector) => match x with (* ax \succ t *)
                                            | dataPorts name1 data => (equiv_decb name1 a)
                                            | _ => false
                                            end) t)) && (existsb (fun x : (dataConnector) => match x with (* bx \succ t *)
                                            | dataPorts name1 data => (equiv_decb name1 b) 
                                            | _ => false
                                            end) t) ||
                                            ((existsb (fun x : (dataConnector) => match x with 
                                            | dataPorts name1 data => (equiv_decb name1 a)
                                            | _ => false
                                            end) t)) && negb(existsb (fun x : (dataConnector) => match x with 
                                            | dataPorts name1 data => (equiv_decb name1 b) 
                                            | _ => false
                                            end) t) then (*caso 1 : existe dataItem p a e p b ou pra ningúem*)
                                              (go s' n acc t)
                                            else
                                              (go (halt [a;b] s') n acc t)
                         end
            end
    end.
  
  (* We define f as the top-level function to be used as follows *)
  Definition f (t: set (set dataConnector)) (pi: set connector) (* : set (set dataConnector) *) := 
   flat_map (go (parse pi []) (length (parse pi [])) []) t. (* (length (parse pi [])) era (length pi) *)

  (* We define the computation of iterations bounded by repetition as follows. *)
  (* It returns the data flow of the connector which immediately preceeds a flow which have already happened.*)
(* Future work - Nu operator
  Definition boundedIteration : set (set dataConnector) ->  set connector -> nat -> (*set dataConnector -> *)
    set ( set (set dataConnector)) -> (set (set dataConnector))  :=
    fix rec t pi iterations resp :=
      match iterations with
      | 0 => last resp t
      | Datatypes.S n => if existsb (subSubset t) resp
                         then (last resp t) 
                         else (rec (f t pi) pi n (resp ++ [t]))
      end.

  Definition boundedIterationTrace : set (set dataConnector) ->  set connector -> nat -> (*set dataConnector -> *)
    set (set (set dataConnector)) -> (set (set (set dataConnector)))  :=
    fix rec t pi iterations resp :=
      match iterations with
      | 0 => resp 
      | Datatypes.S n => if existsb (subSubset t) resp then [last resp t] else (rec (f t pi) pi n (resp ++ [t]))
      end. *)

  (** Syntatic definitions **)
  (* We formalize syntatic programs as pi and its operators *)
  (* sProgram stands for simple program *)

  Inductive syntaticProgram :=
  | sProgram : reoProgram -> syntaticProgram
 (*  | nu : reoProgram -> syntaticProgram *)
  | star : reoProgram -> syntaticProgram.

  Notation "# pi" := (sProgram pi) (no associativity, at level 69).
  (* Notation "nu. pi" := (nu pi) (no associativity, at level 69). *)
  Notation "pi *" := (star pi) (no associativity, at level 69).

  (* We define our logic's syntax formulae based on classic modal logic's connectives *)
  Inductive formula :=
  | proposition : (*Prop*) nat -> formula
  | box : set dataConnector -> syntaticProgram -> formula -> formula
  | diamond : set dataConnector -> syntaticProgram -> formula -> formula
  | and : formula -> formula -> formula
  | or : formula -> formula -> formula
  | neg : formula -> formula
  | impl : formula -> formula -> formula
  | biImpl : formula -> formula -> formula.
  (*02/03 - BNF sintática parece ok. notação do diamond tá bugada *)

  Context `{EqDec formula eq}.

  Notation " < t , pi >" := (diamond t pi) (left associativity, at level 69).
  Notation " [' t , pi ']" := (box t pi) (no associativity, at level 69).

  Notation " a ---> b" := (impl a b) (left associativity, at level 79).

  (* We provide a proposition to state a data item of a port *)

  Definition dataFromPorts (data: dataConnector) :=
    match data with
    | dataPorts a x => x
    | fifoData a x b => x
    end.

  Definition dataInPort (n: dataConnector) (d:data): Prop := 
    dataFromPorts n = d. 

  Definition dataInFifo (n: dataConnector) (d: data) : Prop :=
    dataFromPorts n = d.

  Fixpoint getData (portsData : set dataConnector) (portName : name) (portData : data) : bool :=
    match portsData with 
    | a::t => match a with
              | dataPorts name data => equiv_decb data portData
              | _ => getData t portName portData
              end
    | _ => false
    end.

  (* We retrieve all states of the model which is related to a state v by R*)
  Fixpoint retrieveRelatedStatesFromV (setStates : set (state * state)) (s : state) 
    : set state :=
    match setStates with 
    | nil => nil
    | a::states => if s == (fst a) then (snd a)::(retrieveRelatedStatesFromV states s) 
                   else retrieveRelatedStatesFromV states s
    end.


  (* We retrieve the verification's initial state based on the data flow t*)
  Fixpoint getInitialStateAux (m:model) (states : set state) (t: set dataConnector) :=
    match states with
    | nil => nil
    | st::states' => if (subset t (delta(Fr m) st)) then st::getInitialStateAux m states' t
                     else getInitialStateAux m states' t
    end.

  Definition getState (m: model) (t: set dataConnector) : set state :=
    getInitialStateAux m (S(Fr(m))) t.

  (*We define RTC for R*)
  Fixpoint getReflexiveAux (states : set state) : set (state * state) :=
    match states with
    | nil => nil
    | a::states' => (a,a)::getReflexiveAux states'
    end.

  Definition getReflexive (m: model) : set (state * state) := set_union equiv_dec (R(Fr(m))) 
                                                  (getReflexiveAux (S(Fr(m)))).


  (*Creates pairs of states (s,a). Will be employed in the Reflexive closure calculation *)
  Fixpoint createNewPair (s : state) (setPairStates : set (state)) :=
    match setPairStates with
    | nil => nil
    | a::relStates => (s,a)::createNewPair s relStates
    end. 

  (* retrieve the states w where s R_\pi w *)
  Fixpoint getNeighbors (s : state) (relR: set (state * state)) : set state :=
    match relR with
    | nil => nil
    | a::relStates => if s == fst(a) then snd(a)::getNeighbors s relStates
                      else getNeighbors s relStates
    end.

  Fixpoint getTransitiveAux' (relR : set (state * state)) (n:nat) (a:state) : set (state) :=
    match n with
    | 0 => nil
    | Datatypes.S m => set_union equiv_dec (getNeighbors a relR) 
                        (flat_map (getTransitiveAux' relR m)(getNeighbors a relR))
    end.

  Fixpoint getTransitiveAux (S: set state) (relR : set (state * state)) : set (state * state) :=
    match S with
    | nil => nil
    | state::otherStates => set_union equiv_dec (createNewPair state (getTransitiveAux' relR (length relR) state)) (getTransitiveAux otherStates relR)
    end. 

  Definition getTransitive (m : model) := 
    getTransitiveAux (S(Fr(m))) (R(Fr(m))). 

  Definition RTC (m:model) : set (state * state) :=
   set_union equiv_dec (R(Fr(m))) (set_union equiv_dec (getTransitive m) (getReflexive m)).


  (*We recover the states reached by means of \nu.pi *)

(*   Definition getNuPiReachedState (m:model) (t: set (set dataConnector)) (reoConnector: set connector) :=
   flat_map (getState (m)) (boundedIteration t reoConnector (length reoConnector * 2) []). *)

  (* The notion of diamond and box satisfaction is defined as follows *)

  Definition diamondSatisfactionPi (m:model) (p : nat) 
    (states : set state) :=
    if (states == []) then false else (*Clausula adicionada p sequencia de estados não encontrada por Nu.Pi, por exemplo *)
    existsb (fun x : state => (V(m)x p)) states.

  Definition boxSatisfactionPi (m:model) (p : nat) 
    (states: set state) :=
    if (states == []) then false else (*Clausula adicionada p sequencia de estados não encontrada por Nu.Pi, por exemplo *)
    forallb (fun x : state => (V(m)x p)) states.

  Notation "x |> f" := (f x) (at level 79, no associativity).


  Fixpoint singleModelStep (m:model) (formula : formula) (s:state) : bool :=
    match formula with
    | proposition p => (V(m) s p)
    | neg p => negb (singleModelStep m p s) 
    | and a b => (singleModelStep m a s) && (singleModelStep m b s)
    | or a b => (singleModelStep m a s) || (singleModelStep m b s)
    | impl a b => negb (singleModelStep m a s) || (singleModelStep m b s)
    | biImpl a b => (negb (singleModelStep m a s) || (singleModelStep m b s)) &&
                    (negb (singleModelStep m b s) || (singleModelStep m a s)) 
    | box t pi p' => match pi with
                  | sProgram reo => match p' with
                                   | proposition p'' => 
                                       boxSatisfactionPi (m) (p'')
                                       (retrieveRelatedStatesFromV (R(Fr(m))) s)
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (R(Fr(m))) s)
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (R(Fr(m))) s)
                                   | and a b => (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) &&
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   | or a b => (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) ||
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   | neg a => negb (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) 
                                   | impl a b => (negb (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))) ||
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   | biImpl a b => (negb (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))) ||
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) &&
                                                   (negb (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))) ||
                                                (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   end
                  | star reo => match p' with
                                   | proposition p'' => 
                                       boxSatisfactionPi (m) (p'')
                                       (retrieveRelatedStatesFromV (RTC(m)) s)
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (RTC(m)) s)
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (RTC(m)) s)
                                   | and a b => (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) &&
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                   | or a b => (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) ||
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                   | neg a => negb (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) 
                                   | impl a b => (negb (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))) ||
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                   | biImpl a b => (negb (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))) ||
                                                (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) &&
                                                   (negb (forallb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))) ||
                                                (forallb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                 end
                  (* | nu reo => match p' with
                                   | proposition p'' => 
                                       boxSatisfactionPi (m) (p'')
                                       (getNuPiReachedState m [t] (program2SimpProgram reo))
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                         (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                         (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))
                                   | and a b => (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))) &&
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | or a b => (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))) ||
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | neg a => negb (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | impl a b => (negb (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) ||
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | biImpl a b => ((negb (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) ||
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) &&
                                                   ((negb (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) ||
                                                (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))))
                                 end *)
                     end
    | diamond t pi p' => match pi with
                  | sProgram reo => match p' with
                                   | proposition p'' => 
                                       diamondSatisfactionPi (m) (p'')
                                       (retrieveRelatedStatesFromV (R(Fr(m))) s)
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (R(Fr(m))) s)
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (R(Fr(m))) s)
                                   | and a b => (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) &&
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   | or a b => (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) ||
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   | neg a => negb (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) 
                                   | impl a b => (negb (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))) ||
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   | biImpl a b => (negb (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))) ||
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s))) &&
                                                   (negb (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))) ||
                                                (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (R(Fr(m))) s)))
                                   end
                  | star reo => match p' with
                                   | proposition p'' => 
                                       diamondSatisfactionPi (m) (p'')
                                       (retrieveRelatedStatesFromV (RTC(m)) s)
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (RTC(m)) s)
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                          (retrieveRelatedStatesFromV (RTC(m)) s)
                                   | and a b => (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) &&
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                   | or a b => (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) ||
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                   | neg a => negb (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) 
                                   | impl a b => (negb (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))) ||
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                   | biImpl a b => (negb (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))) ||
                                                (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s))) &&
                                                   (negb (existsb (singleModelStep m b)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))) ||
                                                (existsb (singleModelStep m a)
                                           ((retrieveRelatedStatesFromV (RTC(m)) s)))
                                 end
                  (* | nu reo => match p' with
                                   | proposition p'' => 
                                       diamondSatisfactionPi (m) (p'')
                                       (getNuPiReachedState m [t] (program2SimpProgram reo))
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                          (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                          (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))
                                   | and a b => (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))) &&
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | or a b => (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))) ||
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | neg a => negb (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | impl a b => (negb (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) ||
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))
                                   | biImpl a b => ((negb (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) ||
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) &&
                                                   ((negb (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo))))) ||
                                                (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m [t] (program2SimpProgram reo)))))
                                   end *)
                  end
      end.

  Lemma singleModelStepSound_1 : forall m, forall n, forall phi, forall s, 
   phi = proposition n /\ (V(m) s n) = true -> singleModelStep m phi s = true.
  Proof.
  intros. destruct H3. rewrite H3. simpl. exact H4.
  Defined.

  Lemma singleModelStepSound_2 : forall m, forall phi, forall phi', forall s, 
   phi = neg phi' /\ (singleModelStep m phi' s) = false -> (singleModelStep m phi s) = true.
  Proof.
  intros. destruct H3. rewrite H3. simpl. rewrite H4. reflexivity.
  Defined.

  Lemma singleModelStepSound_3 : forall m, forall phi, forall phi', forall phi'', forall s,
  phi = (and phi' phi'') /\ ((singleModelStep m phi' s) && (singleModelStep m phi'' s)) = true
    ->  (singleModelStep m phi s) = true.
  Proof.
  intros. destruct H3. rewrite H3. simpl. exact H4.
  Defined.

  Lemma singleModelStepSound_4 : forall m, forall phi, forall phi', forall phi'', forall s,
  phi = (or phi' phi'') /\ ((singleModelStep m phi' s) || (singleModelStep m phi'' s)) = true
    ->  (singleModelStep m phi s) = true.
  Proof.
  intros. destruct H3. rewrite H3. simpl. exact H4.
  Defined.

  Lemma singleModelStepSound_5 : forall m, forall phi, forall phi', forall phi'', forall s,
  phi = (biImpl phi' phi'') /\ (negb (singleModelStep m phi' s) || (singleModelStep m phi'' s)) &&
                               (negb (singleModelStep m phi'' s) || (singleModelStep m phi' s))  = true
    ->  (singleModelStep m phi s) = true.
  Proof.
  intros. destruct H3. rewrite H3. simpl. exact H4.
  Defined.

  Lemma singleModelStepSound_6 : forall m, forall phi, forall phi', forall phi'', forall s,
  phi = (or phi' phi'') /\ ((singleModelStep m phi' s) || (singleModelStep m phi'' s)) = true
    ->  (singleModelStep m phi s) = true.
  Proof.
  intros. destruct H3. rewrite H3. simpl. exact H4.
  Defined.

  (* The evaluation of an atomic formula is done as follows *)

  Definition singleFormulaVerify (m : model) (p : formula) 
    (t: set dataConnector) : bool :=
    (forallb (fun x => eqb x true) (map (singleModelStep m p) (getState m t))).

  (*We formalize the logic's axioms as the inductive type "formula" *)

  (*Dynamic Logic Axioms*)

  Definition axiomK (phi: option formula) : option formula :=
    match phi with
    | Some (box t pi (impl phi' phi'')) => Some (impl (box t pi phi') (box t pi phi''))
    | _ => None
    end.

  Definition axiomAnd (phi : option formula) : option formula :=
    match phi with
    | Some (box t pi (and phi' phi'')) => Some ( and (box t pi phi') (box t pi phi''))
    | _ => None
    end.

  Definition axiomDu (phi: option formula) : option formula :=
    match phi with
    | Some (box t pi (neg phi')) => Some (neg (diamond t pi phi'))
    | Some (neg (diamond t pi phi')) => Some (box t pi (neg phi') )
    | _ => None
    end.


  Definition axiomR (phi: option formula) : option formula :=
    match phi with
    | Some (diamond t pi phi) => Some phi
    | _ => None
    end.

  Definition axiomIt (phi: option formula) : option formula :=
    match phi with
    | Some (and (phi') (box t (sProgram pi) (box t' (star pi') phi''))) => if (equiv_decb phi' phi'')(*&&
        (equiv_decb pi pi') then *) then
        Some (box t (star pi') phi') else None (*ERICK: da erro se usarmos a mesma
variavel no pattern matching em dois lugares diferentes.R: usar variaveis diferentes e forçar a ser igual.*)
    | Some (box t (star pi) phi') => Some (and (phi') (box t (sProgram pi) (box t (star pi) phi')))
    | _ => None
    end.  

  (*29/07/2020 os axiomas não serão usados aqui
    para provas sintáticas. Isso vai ficar pro nosso Tableaux *)

  Definition axiomInd (phi: option formula) : option formula :=
    match phi with
    | Some (and (phi') (box t pi (impl (phi'') (box t' (star pi') phi''')))) => Some (box t (star pi') phi')
    | _ => None
    end.

  End LogicMain.
  Section ModelExecution.

  Variable name state data: Type.
  Context `{EqDec name eq} `{EqDec data eq} `{EqDec state eq}.
 
  (* A model checker for ReLo *)

  Definition emptyLambda (s : state) (n: name) := 0%Q.

  Definition emptyDelta (s : state) : set (dataConnector name data) := [].
 
  Definition emptyVal (s : state) (prop : nat) : bool := false.

  Definition emptyModel := mkmodel ( mkframe [] [] emptyLambda emptyDelta ) (emptyVal).

  Check emptyModel.

  (*ERICK: rodar a função abaixo p todas as portas do modelo que estão em T*)

  Definition retrieveSinglePortProp (t : set (dataConnector name data)) (index : nat) (n : name)
    : set (nat * Prop) :=
    match t with
    | [] => []
    | a::t' => match a with
               | dataPorts a x => if (n == a) then [(Datatypes.S  (index), dataInPort (dataPorts n x) x)] else []
               | fifoData a x b => []
               end
    end.

  Definition sameData (n1 : (dataConnector name data)) (n2 : (dataConnector name data)) : bool :=
    match n1,n2 with
    | dataPorts a x, dataPorts b y => (* (nequiv_decb a b) && *) (equiv_decb x y)
    | _, _ => false
    end.

  Definition portsHaveSameData (n1 : (dataConnector name data)) (n2 : (dataConnector name data)) : Prop :=
    match n1,n2 with
    | dataPorts a x, dataPorts b y => (dataInPort (dataPorts a x) x) = (dataInPort (dataPorts b y) y)
    | _ , _ => False
    end.
    
  Fixpoint retrieveTwoPortsProp  (index:nat) (t: set (dataConnector name data)) 
    (n : (dataConnector name data)) : set (nat * Prop) :=
    match t with
    | [] => []
    | a::t' => if (sameData n a) then [(index, portsHaveSameData a n)]++(retrieveTwoPortsProp index t' n)
               else (retrieveTwoPortsProp index t' n)
    end.

  Fixpoint constructSetOfStates (phi: formula (set (dataConnector name data))
    (syntaticProgram name)) (n: nat) : set nat :=
    match phi with 
    | proposition _ _ p => [n]
    | neg p => set_add equiv_dec (n) (constructSetOfStates p (n))
    | and a b => set_union equiv_dec (set_add equiv_dec (n) (constructSetOfStates a (n))) 
                                     (set_add equiv_dec (n) (constructSetOfStates b (n)))
    | or a b => set_union equiv_dec (set_add equiv_dec (n) (constructSetOfStates a (n))) 
                                     (set_add equiv_dec (n) (constructSetOfStates b (n)))
    | impl a b => set_union equiv_dec (set_add equiv_dec (n) (constructSetOfStates a (n))) 
                                     (set_add equiv_dec (n) (constructSetOfStates b (n)))
    | biImpl a b => set_union equiv_dec (set_add equiv_dec (n) (constructSetOfStates a (n))) 
                                     (set_add equiv_dec (n) (constructSetOfStates b (n)))
    | box t pi p' => set_add equiv_dec (n) (constructSetOfStates p' (Datatypes.S n))
    | diamond t pi p' => set_add equiv_dec (n) (constructSetOfStates p' (Datatypes.S n))
  end.

  (* Equality relation for data items *)
  Program Instance dataConnectorEqDec {name} {data} `(eqa : EqDec name eq) `(eqb: EqDec data eq) : EqDec (dataConnector name data) eq :=
    { equiv_dec :=
      fix rec (x y : dataConnector name data) :=
      match x,y with
      | dataPorts a b, dataPorts c d => if a == c then if b == d then in_left else in_right else in_right
      | fifoData a x b, fifoData c y d => if a == c then if b == d then if x == y 
                                          then in_left else in_right else in_right else in_right
      | dataPorts a b, fifoData c y d | fifoData c y d , dataPorts a b => in_right
      end
    }.

  (* We also consider FIFO entries to derive propositions *)

  Definition dataInFIFO (n1 : (dataConnector name data)) (n2 : (dataConnector name data)) : Prop :=
    if (equiv_decb n1 n2) then 
      match n1,n2 with
      | fifoData a x b, fifoData c y d => dataInFifo (fifoData a x b) x
      | _, _ => False
      end
    else False.

  Fixpoint retrieveFIFOdataProp (index: nat) (t: set (dataConnector name data)) 
    (n : dataConnector name data) : set (nat * Prop) :=
    match t with
    | fifodata::t' => match fifodata with
                    | fifoData a x b => if (equiv_decb fifodata n) then [(index, dataInFIFO fifodata n)]++(retrieveFIFOdataProp index t' n)
                                        else (retrieveFIFOdataProp index t' n)
                    | dataPorts a b => (retrieveFIFOdataProp index t' n)
                    end
    | [] => []
    end.

  Definition buildValidPropositions (N: set name) (index: nat) (t: set (dataConnector name data)) 
     : set (nat * Prop) :=
    ((flat_map(retrieveTwoPortsProp index t) (t)) ++ 
    (flat_map(retrieveSinglePortProp t index) (N))) ++
    (flat_map(retrieveFIFOdataProp index t) t).

  Fixpoint getProp (setProp: set (nat * Prop)) (n: nat) : bool :=
    match setProp with  
    | [] => false
    | a::t => if (fst(a) == n) then true else getProp t n
    end.

  (*aqui teremos dois nat: um indicando o index das proposições e p o que denota a proposição em si. *)
  (*ERICK: Aparentemente tem dois indices repetidos ali embaixo:
    index: estado que quero calcular
    s ;estado a avaliar (pela assinatura da função. A grosso modo, S = index)
    p : prop -> verificar*)
   Definition getValFunctionProp (N: set name) (t:set (dataConnector name data)) (index: nat) (s:nat) (p:nat) :=
    getProp ((buildValidPropositions N index t )) p.

  Definition setStateForProp (s: nat) := [s].

  Definition lambdaForProp (s :nat) (n: name) := (Qmake 0 1).

  (* The markup for a single state is the same input markup *)
  Definition deltaForProp (t: set (dataConnector name data)) (s:nat) := t.

  Definition buildPropFrame (t: set (dataConnector name data)) (s:nat) := 
    mkframe (setStateForProp s) ([]) (lambdaForProp)
    (deltaForProp t).

  (* The construction of the model is done by the following definition *)

  Definition buildPropModel (N: set name)(t: set (dataConnector name data)) (s:nat) :=
    mkmodel (buildPropFrame t s) (getValFunctionProp N t s).

  (*Auxiliary function employed by the function below it*)

  Fixpoint getDelta (dataMarkups : set (nat * (set (dataConnector name data)))) (state: nat) :=
    match dataMarkups with
    | [] => []
    | dataMarkup::moreData => if fst(dataMarkup) == state then ((snd(dataMarkup))) else getDelta moreData state
    end.

  (*We may also construct composite models by joining states and the relation between them *)
  (*props : set of states and the propositions that hold in them.*)
  Fixpoint getValFunction (props : set (nat * (set nat))) (state : nat) (prop: nat) :=
    match props with
    | [] => false
    | stateAndProp::moreProps => if fst(stateAndProp) == state then
                                  set_mem equiv_dec (prop) (snd(stateAndProp))
                                 else getValFunction moreProps state prop
    end.

  (*ERICK: a ideia é computar primeiro o conjunto nat * Prop onde tenho o mapa das proposições para um índice natural. Depois,
    preciso calcular o mapa nat * set nat, onde nat é o estado e set nat é o conjunto de proposições válidas naquele estado.*)

  (* Auxiliary record to hold the global index of props*)
  Record calcProps := mkcalcProps {
    statesAndProps : set (nat * (set nat));
    propCounter : nat
  }.

  (*Returns the index of propositions construted at a specific state *)
  Fixpoint getIndexOfProps (setProps: set (nat * Prop)) : set nat :=
    match setProps with
    | [] => []
    | prop::moreProps => set_union equiv_dec [fst(prop)] (getIndexOfProps moreProps)
    end.

  Definition getNewValFunc (calc: calcProps) (N: set name) (t:set (set (dataConnector name data))) (state: nat) :=
  mkcalcProps (set_add equiv_dec (state,getIndexOfProps(flat_map (buildValidPropositions N (propCounter(calc))) t)) (statesAndProps calc)) 
              (propCounter(calc) + length (getIndexOfProps(flat_map (buildValidPropositions N state) t))).

   Definition addInfoToModel (m: model name nat data) (origin:nat) (dest: nat) 
    (N: set name) (t: (set (dataConnector name data))) (dataMarkups : (set (nat * (set (dataConnector name data)))))
    (calc : calcProps) :=
    mkmodel 
      (mkframe (set_add equiv_dec dest (S(Fr(m)))) (set_add equiv_dec (origin,dest) (R(Fr(m)))) (lambda(Fr(m))) 
      (getDelta dataMarkups))
      (getValFunction (statesAndProps (getNewValFunc calc N [t] dest))).
  (*ERICK: o [t] é para reaproveitar o que já funciona *)

(*   Definition concatenateModels (m1: model name nat data) (m2: model name nat data) (t: set (set(dataConnector name data))) 
    (n: set name) (index : nat) (dataMarkups : (set (nat * (set (dataConnector name data))))) :=
    (*ERICK: Corrigir o uso de t na getValFunctionProp na função abaixo*)
    mkmodel 
      (mkframe (set_union equiv_dec (S(Fr(m1))) (S(Fr(m2)))) (set_union equiv_dec (R(Fr(m1))) (R(Fr(m2)))) 
        (lambda(Fr(m1))) (getDelta dataMarkups)) (getValFunctionProp n (hd [] t) index). *)


  (* The following definition is employed in deriving the model of neg p based on the model for p, 
      p a proposition *)
  Fixpoint negatePropositions (setProps: set (nat * Prop)) :=
    match setProps with
    | [] => []
    | prop::moreProps => [~ (snd prop)] ++ (negatePropositions moreProps)
    end.

  (*Given a set of already visited states and a data markup, we return the corresponding state if it has already been reached*)

  Fixpoint getVisitedState (t : set (set (dataConnector name data))) 
      (visStates: set (nat * set (set (dataConnector name data)))) : option nat :=
  match visStates with
  | [] => None
  | visState::moreStates => if (set_eq t (snd(visState))) then Some (fst(visState)) else getVisitedState t moreStates
  end.

  Fixpoint getVisitedStateAux (t : (set (dataConnector name data))) (setData : set (set (dataConnector name data))) :=
    match setData with
    | [] => false
    | a::moreData => equiv_decb t a  || getVisitedStateAux t moreData
    end.

  Fixpoint getVisitedState' (t : (set (dataConnector name data))) 
      (visStates: set (nat * (set (dataConnector name data)))) : option nat :=
  match visStates with
  | [] => None
  | visState::moreStates => if equiv_decb t (snd(visState)) then Some(fst(visState)) else getVisitedState' t moreStates
  end.

  (* We retrieve all stats in a iteration step, whether they have been visited or not*)

  Fixpoint getVisitedStates (t : set (set (dataConnector name data))) 
      (visStates: set (nat * (set (dataConnector name data)))) :=
    match t with
    | [] => []
    | visState::moreStates => ((getVisitedState' visState visStates), visState)::(getVisitedStates moreStates visStates)
    end.

  Check getVisitedStates.

  (* Now a new index is allocated to the ones not visitated - Only useful to get destination states *)
  (* Erick : Talvez o problema do não deterministico esteja aqui *)
  Fixpoint liftIndex (index : nat) (currentStates : set (option nat * set (dataConnector name data))) := 
    match currentStates with
    | [] => []
    | visState::moreStates => match (fst(visState)) with
                              | None => (index, (snd(visState)))::(liftIndex (Datatypes.S index) moreStates)
                              | Some a => (a,(snd(visState)))::(liftIndex index moreStates)
                              end 
    end.

  Check liftIndex.

  Definition getNewIndexesForStates (t : set (set (dataConnector name data))) 
      (visStates: set (nat * (set (dataConnector name data)))) (index : nat) :=
  liftIndex index (getVisitedStates t visStates).


  (*Retrieve the next global index available based on the visited states*)
  Fixpoint getNextIndex (visStates: set (nat * (set (dataConnector name data)))) (index : nat) :=
    match visStates with
    | [] => index
    | visitedState::moreStates => if Nat.ltb index (fst(visitedState)) then getNextIndex moreStates (fst(visitedState)) 
                              else getNextIndex moreStates (index) 
    end.


  (*We need to apply all intermediate processing steps to each dataFlow reached:*)

  (*Auxiliary definition to calculate the new index, based on the quantities of states that have not been visited in the current iteration *)
  Fixpoint calculateAmountNewStates (visStates: set (nat * (set (dataConnector name data)))) (baseNat : nat) :=
    match visStates with
    | [] => Datatypes.S baseNat
    | visState::moreStates => if Nat.ltb baseNat (fst(visState)) then calculateAmountNewStates moreStates (fst(visState)) 
                              else calculateAmountNewStates moreStates (baseNat) 
    end.

  (*Gets the current origin (i.e., the current state of a data markup) *)

  Fixpoint getOrigin (t: set (dataConnector name data)) (visitedStates : (set (nat * (set (dataConnector name data))))) :=
    match visitedStates with
    | [] => 0
    | state::moreStates => if equiv_decb t (snd(state)) then (fst(state)) else getOrigin t moreStates
    end.

  Fixpoint processIntermediateStep (m: model name nat data) (origin : nat) 
    (N: set name) (visitedStates : (set (nat * (set (dataConnector name data)))))
    (calc : calcProps) (nextSetOfStates : set (nat * set (dataConnector name data))) 
    (*NextSetOfStates : destino de um t normal aqui*):= 
    match nextSetOfStates with 
    | [] => (m, (visitedStates,calc))
    | currentState::moreStates => processIntermediateStep (addInfoToModel m origin (fst(currentState)) N (snd(currentState))
                                      (set_add equiv_dec ((fst(currentState)),(snd(currentState))) visitedStates) calc)
              origin N (set_add equiv_dec ((fst(currentState)),(snd(currentState))) visitedStates)
              (*begin calc*)
              (getNewValFunc calc N [(snd(currentState))] (fst(currentState)))
              (*end calc*)
              moreStates
    end.

  (*Now we need to glue the pieces together to process the entire current states obtained by f(t)*)
  (*Change : Calc is now also output by processGeneralStep *)

  Fixpoint processGeneralStep (m: model name nat data) (N: set name)(visitedStates : (set (nat * (set (dataConnector name data)))))
  (calc : calcProps) (currentSetOfStates : set (nat * set (dataConnector name data)))
  (pi : (reoProgram name)) (index : nat) :=
  match currentSetOfStates with 
  | [] => (m, (visitedStates,(index,calc)))
  | currentState::moreStates => processGeneralStep (fst(processIntermediateStep m (fst(currentState)) N visitedStates calc
                                      (getNewIndexesForStates (f([snd(currentState)])(program2SimpProgram (pi))) visitedStates index))) N
                                      (fst(snd(processIntermediateStep m (fst(currentState)) N visitedStates calc
                                      (getNewIndexesForStates (f([snd(currentState)])(program2SimpProgram (pi))) visitedStates index)))) 
                                      (*begin calc*)                                        
                                      (snd(snd(processIntermediateStep m (fst(currentState)) N visitedStates calc
                                      (getNewIndexesForStates (f([snd(currentState)])(program2SimpProgram (pi))) visitedStates index)))) 
                                      (*end calc*)
                                      (moreStates) pi
                                      (*Abaixo recalcula o index pro próximo estado*)
                                      (calculateAmountNewStates (fst(snd(processIntermediateStep m (fst(currentState)) N visitedStates calc
                                      (getNewIndexesForStates (f([snd(currentState)])(program2SimpProgram (pi))) visitedStates index)))) index) 
  end.

  Fixpoint getModel' (m: model name nat data)  (n: set name) (t: set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) :=
    (*setStates : set of already visited states *)
    match phi with
    | proposition _ _ p => m
    | diamond t' pi p => match pi with
                        | sProgram pi' => getModel' (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        | star pi' => getModel' (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        end
    | box t' pi p => match pi with 
                        | sProgram pi' => getModel' (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index)))
                                          (*calc begin*) 
                                          (snd(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index)))))
                                          (*calc end*) 
                        | star pi' => getModel' (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index)))
                                          (*calc begin*) 
                                          (snd(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index)))))
                                          (*calc end*)
                        end

    (*First Calcuate the model of a, followed by the model of b. might need the set of states and calc as well -not required as they
      have the same starting point.*)
    | and a b | or a b | impl a b | biImpl a b => (getModel' (getModel' m n t index a setStates calc) n t index b setStates calc)
    | neg a => (getModel' m n t index a setStates calc)
    end.

  Fixpoint testGetModel (m: model name nat data)  (n: set name) (t: set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) :=
    (*setStates : set of already visited states *)
    (*This is the new version of old "getVisitedStates"*)
    match phi with
    | proposition _ _ p => setStates
    | diamond t' pi p => match pi with
                        | sProgram pi' => testGetModel (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *)
                                           (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) )))) 
                                          (*calculateAmountNewStates (setStates) index*)
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        | star pi' => testGetModel (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *)
                                           (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) )))) 
                                          (*calculateAmountNewStates (setStates) index*)
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        end
    | box t' pi p => match pi with 
                        | sProgram pi' => testGetModel (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *)
                                           (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) )))) 
                                          (*calculateAmountNewStates (setStates) index*)
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        | star pi' => testGetModel (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *)
                                           (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) )))) 
                                          (*calculateAmountNewStates (setStates) index*)
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        end
    (*First Calcuate the model of a, followed by the model of b. might need the set of states and calc as well.*)
    | and a b | or a b | impl a b | biImpl a b => (testGetModel (getModel' m n t index a setStates calc) n t index b setStates calc)
    | neg a => (testGetModel m n t index a setStates calc) 
    end.

  (*ONGOING: Iteration of programs - Useful for the model construction (the standard star verification is done by means of the RTC) *)

  Fixpoint expandStarFormulas (m : model name nat data) (n : set name) (t : set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) (upperBound : nat) :=
    (*upperBound - limits the search space for \star if no satisfiable model could be found until <upperBound> iterations *)
    (* singleModelStep (m:model) (formula : formula) (s:state) *)
    match upperBound with
    | 0 => ( m, ([], upperBound))
    | Datatypes.S k => match phi with
                       | box t' pi p => match pi with
                                        | sProgram pi' => 
                                        (*Enters this condition afther the first box has been added from the condition below *)
                                        (* This branch is only executed for box added from within expandStarFormulas *)
                                                        if singleModelStep (getModel' m n t index (phi) setStates calc) 
                                                        (phi)
                                                        (*Retrieve the state denoted by T in the model
                                                          TODO Próximo passo, considerar que pode ter mais de um estado aqui...*) 
                                                        (getOrigin (hd [] t) setStates) then
                                                      (* singleModelStep *) 
                                                      ((getModel' m n t index (phi) setStates calc),(setStates,upperBound)) else 
                                                      expandStarFormulas m n t index (box t' (sProgram pi') phi) setStates calc k
                                        | star pi' => if singleModelStep (getModel' m n t index (p) setStates calc) 
                                                        (p)
                                                        (*Retrieve the state denoted by T in the model
                                                          Próximo passo, considerar que pode ter mais de um estado aqui...*) 
                                                        (getOrigin (hd [] t) setStates) then
                                                      (* singleModelStep *) 
                                                      ((getModel' m n t index (p) setStates calc),(setStates,upperBound)) else 
                                                      expandStarFormulas m n t index (box t' (sProgram pi') p) setStates calc k
                                         end
                       | diamond t' pi p => match pi with
                                        | sProgram pi' => 
                                        (*Enters this condition afther the first box has been added from the condition below *)
                                        (* This branch is only executed for box added from within expandStarFormulas *)
                                                        if singleModelStep (getModel' m n t index (phi) setStates calc) 
                                                        (phi)
                                                        (*Retrieve the state denoted by T in the model
                                                          TODO Próximo passo, considerar que pode ter mais de um estado aqui...*) 
                                                        (getOrigin (hd [] t) setStates) then
                                                      (* singleModelStep *) 
                                                      ((getModel' m n t index (phi) setStates calc),(setStates,upperBound)) else 
                                                      expandStarFormulas m n t index (diamond t' (sProgram pi') phi) setStates calc k
                                        | star pi' => if singleModelStep (getModel' m n t index (p) setStates calc) 
                                                        (p)
                                                        (*Retrieve the state denoted by T in the model
                                                          Próximo passo, considerar que pode ter mais de um estado aqui...*) 
                                                        (getOrigin (hd [] t) setStates) then
                                                      (* singleModelStep *) 
                                                      ((getModel' m n t index (p) setStates calc),(setStates,upperBound)) else 
                                                      expandStarFormulas m n t index (diamond t' (sProgram pi') p) setStates calc k
                                         end
                       (* Should not enter here*) 
                       | _ => ( m, (setStates, 0))
                       end
    end.


(*TODO falta definir a getModel p juntar getModel' e expandStarFormulas *)
(*   Definition constructModel (n: set name) (t: set (set (dataConnector name data)))  
    (phi: (formula name data)) :=
    getModel' (buildPropModel n (hd [] t) 0) n t 0 phi ([(0,t)]) (mkcalcProps [] 0). *)

 Fixpoint getCalc (m: model name nat data)  (n: set name) (t: set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) :=
    (*setStates : set of already visited states *)
    match phi with
    | proposition _ _ p => calc
    | diamond t' pi p => match pi with
                        | sProgram pi' => getCalc (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) 
                                          (*calc*)
                                          (snd(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*end calc*)
                        | star pi' => getCalc (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (calculateAmountNewStates (getNewIndexesForStates t setStates index) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi'))) (calculateAmountNewStates (getNewIndexesForStates t setStates index) index)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        end
    | box t' pi p => match pi with 
                        | sProgram pi' =>getCalc (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) 
                                          (*calc*)
                                          (snd(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*end calc*)
                        | star pi' => getCalc (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *) 
                                          (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) 
                                          (*calc*)
                                          (snd(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) ))))
                                          (*end calc*)
                        end
    | _ => calc
    end.

  End ModelExecution.
  End ReoLogicCoq.

Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
