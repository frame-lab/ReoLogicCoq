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

(*Module LogicMain.*)
(*   Section ReoLogicCoq. *)

  Section LogicMain.

  Variable name state data: Type.
  Context `{EqDec name eq} `{EqDec data eq} `{EqDec state eq}.

  Context `{EqDec (data -> data) eq} (Hfil: `{EqDec (data -> bool) eq}).

  Inductive connector :=
  | sync : name -> name -> connector
  | lossySync : name -> name -> connector
  | fifo : name -> name -> connector
  | syncDrain : name -> name -> connector
  | asyncDrain : name -> name -> connector
  | filterReo : (data -> bool) -> name -> name -> connector (*renamed to FilterReo otherwise Coq gets lost with filter for lists*)
  | transform : (data -> data) -> name -> name -> connector
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
      | merger a b c, merger d e f => if a == d then if b == e then if c == f 
                                      then in_left else in_right else in_right else in_right
      | replicator a b c, replicator d e f => if a == d then if b == e then if c == f
                                              then in_left else in_right else in_right else in_right
      | transform f a b, transform g c d =>  if f == g then if a == c then if b == d 
                                             then in_left else in_right else in_right else in_right
      | filterReo f a b, filterReo g c d =>  if f == g then if a == c then if b == d 
                                             then in_left else in_right else in_right else in_right
      | sync a b, lossySync c d | sync a b, fifo c d | sync a b, syncDrain c d | sync a b, asyncDrain c d => in_right
      | sync a b, merger c d e | sync a b, replicator c d e | sync a b, transform c d e 
      | sync a b, filterReo c d e => in_right

      | lossySync a b, sync c d | lossySync a b, fifo c d | lossySync a b, syncDrain c d | lossySync a b, asyncDrain c d => in_right
      | lossySync a b, merger c d e | lossySync a b, replicator c d e | lossySync a b, transform c d e 
      | lossySync a b, filterReo c d e => in_right

      | fifo a b, sync c d | fifo a b, lossySync c d | fifo a b, syncDrain c d | fifo a b, asyncDrain c d => in_right
      | fifo a b, merger c d e | fifo a b, replicator c d e | fifo a b, transform c d e
      | fifo a b, filterReo c d e => in_right

      | syncDrain a b, sync c d | syncDrain a b, lossySync c d | syncDrain a b, fifo c d | syncDrain a b, asyncDrain c d => in_right
      | syncDrain a b, merger c d e | syncDrain a b, replicator c d e 
      | syncDrain a b, transform c d e | syncDrain a b, filterReo c d e  => in_right

      | asyncDrain a b, sync c d | asyncDrain a b, lossySync c d | asyncDrain a b, fifo c d | asyncDrain a b, syncDrain c d => in_right
      | asyncDrain a b, merger c d e | asyncDrain a b, replicator c d e
      | asyncDrain a b, transform c d e | asyncDrain a b, filterReo c d e => in_right

      | merger a b c, sync d e | merger a b c, lossySync d e | merger a b c, fifo d e | merger a b c, syncDrain d e => in_right
      | merger a b c, asyncDrain d e  => in_right
      | merger a b c, replicator d e f => in_right
      | merger a b c, transform f d e | merger a b c, filterReo f d e  => in_right

      | replicator a b c, sync d e | replicator a b c, lossySync d e | replicator a b c, fifo d e | replicator a b c, syncDrain d e => in_right
      | replicator a b c, asyncDrain d e => in_right 
      | replicator a b c, merger d e f   => in_right
      | replicator a b c, transform f d e | replicator a b c, filterReo f d e => in_right

      | filterReo a b c, sync d e | filterReo a b c, lossySync d e | filterReo a b c, fifo d e | filterReo a b c, syncDrain d e => in_right
      | filterReo a b c, asyncDrain d e  => in_right
      | filterReo a b c, merger d e f => in_right
      | filterReo a b c, replicator d e f | filterReo a b c, transform d e f => in_right

      | transform a b c, sync d e | transform a b c, lossySync d e | transform a b c, fifo d e | transform a b c, syncDrain d e => in_right
      | transform a b c, asyncDrain d e  => in_right
      | transform a b c, merger d e f => in_right
      | transform a b c, replicator d e f | transform a b c, filterReo d e f => in_right
      end
    }.

  (* We define a type which denotes the ports to fire and their respective data *)
  Inductive goMarks :=
    | goTo : name -> name -> goMarks
    | goFifo : name -> data -> name -> goMarks  (*enters fifo: axb*)
    | goFromFifo : name -> data -> name -> goMarks (*leaves fifo : axb->b *)
    | goTransform : (data -> data) -> name -> name -> goMarks
    | goFilter : (data -> bool) -> name -> name -> goMarks.
 
  (* We define an inductive type for the data that effectively denote the flow of a 
   circuit: either there are data items on some port names or a data item within a
   buffer *)
  Inductive dataConnector :=
    | fifoData : name -> data -> name -> dataConnector
    | dataPorts : name -> data -> dataConnector.

  (*Denotes propositional symbols' value in this ReLo implementation*)
  Inductive dataProp name data :=
    | dataInFifo : name -> data -> name -> dataProp name data
    | dataInPorts : name -> data -> dataProp name data
    | dataBothPorts : name -> name -> dataProp name data.
  (*Qui formuale needs to keep track also of the formulae they are rewriting*)
(*     | quiFormulaBox : nat -> (dataProp name data) -> dataProp name data
    | quiFormulaDia : nat -> (dataProp name data) -> dataProp name data. *)

 Program Instance dataProp_eqdec `(eqa: EqDec name eq) `(eqb: EqDec data eq) : EqDec (dataProp name data) eq :=
  {
    equiv_dec x y (* := fix rec x y *) :=
      match x, y with
        | dataInPorts a x, dataInPorts b y => if a == b then if x == y then in_left else in_right else in_right
        | dataInFifo a x b, dataInFifo c y d => if a == c then if b == d then if x == y then in_left else in_right else in_right else in_right
        | dataBothPorts _ a b, dataBothPorts _ c d => if a == c then if b == d then in_left else in_right else in_right
        | dataInPorts a x , dataInFifo b y c => in_right
        | dataInPorts a x , dataBothPorts _ b y => in_right
        | dataInFifo a x b , dataInPorts c y => in_right
        | dataInFifo a x b , dataBothPorts _ c y => in_right
        | dataBothPorts _ a b , dataInPorts c y => in_right
        | dataBothPorts _ a b , dataInFifo c y d  => in_right
      end
  }.

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
  Record model := mkmodel {
    Fr  : frame;
    V : state -> (* nat *) (dataProp name data) -> bool 
  }.


  (*06/04 - Redesign of Reo programs as \pi = (f,b) *)

  Inductive flowProgram :=
    | flowSync : name -> name -> flowProgram
    | flowLossySync : name -> name -> flowProgram
    | flowFifo : name -> name -> flowProgram
    | flowMerger : name -> name -> name -> flowProgram
    | flowReplicator : name -> name -> name -> flowProgram
    | flowTransform : (data -> data) -> name -> name -> flowProgram
    | flowFilter : (data -> bool) -> name -> name -> flowProgram.

  Program Instance flowProgram_eqdec `{EqDec name eq} : EqDec flowProgram eq :=
  { equiv_dec x y :=
    match x, y with
    | flowSync a b, flowSync c d => if a == c then if b == d then in_left else in_right else in_right
    | flowLossySync a b, flowLossySync c d => if a == c then if b == d then in_left else in_right else in_right
    | flowFifo a b, flowFifo c d => if a == c then if b == d then in_left else in_right else in_right
    | flowMerger a b c, flowMerger d e f => if a == d then if b == e then if c == f
                                            then in_left else in_right else in_right else in_right
    | flowReplicator a b c, flowReplicator d e f => if a == d then if b == e then if c == f
                                            then in_left else in_right else in_right else in_right
    | flowTransform f a b, flowTransform g c d => if f == g then if a == c then if b == d
                                                  then in_left else in_right else in_right else in_right
    | flowFilter f a b, flowFilter g c d => if f == g then if a == c then if b == d
                                                  then in_left else in_right else in_right else in_right 
 
    | flowSync a b, flowLossySync c d | flowSync a b, flowFifo c d => in_right
    | flowSync a b, flowMerger c d e | flowSync a b, flowReplicator c d e 
    | flowSync a b, flowTransform c d e | flowSync a b, flowFilter c d e => in_right

    | flowLossySync a b, flowSync c d | flowLossySync a b, flowFifo c d => in_right
    | flowLossySync a b, flowMerger c d e | flowLossySync a b, flowReplicator c d e 
    | flowLossySync a b, flowTransform c d e | flowLossySync a b, flowFilter c d e => in_right

    | flowFifo a b, flowSync c d | flowFifo a b, flowLossySync c d => in_right
    | flowFifo a b, flowMerger c d e | flowFifo a b, flowReplicator c d e
    | flowFifo a b, flowTransform c d e | flowFifo a b, flowFilter c d e => in_right


    | flowReplicator a b c, flowSync d e => in_right
    | flowReplicator a b c, flowLossySync d e => in_right
    | flowReplicator a b c, flowFifo d e => in_right
    | flowReplicator a b c, flowMerger d e f => in_right
    | flowReplicator a b c, flowTransform d e f | flowReplicator a b c, flowFilter d e f  => in_right

    | flowMerger a b c, flowSync d e => in_right
    | flowMerger a b c, flowLossySync d e => in_right
    | flowMerger a b c, flowFifo d e => in_right
    | flowMerger a b c, flowReplicator d e f => in_right
    | flowMerger a b c, flowTransform d e f | flowMerger a b c, flowFilter d e f => in_right

    | flowTransform a b c, flowSync d e => in_right
    | flowTransform a b c, flowLossySync d e => in_right
    | flowTransform a b c, flowFifo d e => in_right
    | flowTransform a b c, flowMerger d e f => in_right
    | flowTransform a b c, flowReplicator d e f | flowTransform a b c, flowFilter d e f  => in_right

    | flowFilter a b c, flowSync d e => in_right
    | flowFilter a b c, flowLossySync d e => in_right
    | flowFilter a b c, flowFifo d e => in_right
    | flowFilter a b c, flowMerger d e f => in_right
    | flowFilter a b c, flowReplicator d e f | flowFilter a b c, flowTransform d e f => in_right
    end}.


  Inductive blockProgram :=
    | flowSyncdrain : name -> name -> blockProgram
    | flowaSyncdrain : name -> name -> blockProgram.

  Program Instance blockProgram_eqdec `{EqDec name eq} : EqDec blockProgram eq :=
  { equiv_dec x y :=
    match x, y with
    | flowSyncdrain a b, flowSyncdrain c d | flowaSyncdrain a b, flowaSyncdrain c d => if a == c then if b == d then in_left else in_right else in_right
    | flowSyncdrain a b, flowaSyncdrain c d | flowaSyncdrain a b, flowSyncdrain c d => in_right
    end}.

  (* Lifting from \pi = (f,b) to \pi *)

  Inductive reoProgram :=
    | reoProg : set flowProgram -> set blockProgram -> reoProgram.


  Program Instance reoProgram_eqdec `{EqDec flowProgram eq} `{EqDec blockProgram eq} : EqDec reoProgram eq :=
  { equiv_dec x y :=
    match x, y with
    | reoProg a b, reoProg c d => if a == c then if b == d then in_left else in_right else in_right
    end}.

  Definition singleFlow2Reo (flowProg : flowProgram) := 
    match flowProg with
    | flowSync a b => sync a b
    | flowLossySync a b => lossySync a b
    | flowFifo a b => fifo a b
    | flowMerger a b c => merger a b c
    | flowReplicator a b c => replicator a b c
    | flowTransform f a b => transform f a b
    | flowFilter f a b => filterReo f a b
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
    | reoProg setFlow setBlock => (block2Reo setBlock)++(flow2Reo setFlow)
     (*  set_union equiv_dec (block2Reo setBlock) (flow2Reo setFlow) *)
    end.

  (* Parsing of a Reo program \pi *)

  (* We define an inductive type for the conversion of a reo Connector to a Reo
     program by means of *parse* function *)

  Inductive program :=
    | to : name -> name -> program (* sync, replicator, merger *)
    | asyncTo : name -> name -> program (* LossySync *)
    | fifoAlt : name -> name -> program (* fifo *)
    | transformTo : (data -> data) -> name -> name -> program
    | filterTo : (data -> bool) -> name -> name -> program
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
      | transformTo f a b, transformTo g c d => if a == c then if b == d then if f == g 
                                                then in_left else in_right else in_right else in_right
      | filterTo f a b, filterTo g c d => if a == c then if b == d then if f == g 
                                                then in_left else in_right else in_right else in_right
      | to a b, asyncTo c d  | to a b, fifoAlt c d 
      | to a b, SBlock c d   | to a b, ABlock c d  => in_right
      | to a b, transformTo g c d | to a b, filterTo g c d  => in_right
      | asyncTo a b, to c d  | asyncTo a b, fifoAlt c d 
      | asyncTo a b, SBlock c d   | asyncTo a b, ABlock c d => in_right
      | asyncTo a b, transformTo g c d | asyncTo a b, filterTo g c d  => in_right
      | fifoAlt a b, asyncTo c d  | fifoAlt a b, to c d 
      | fifoAlt a b, SBlock c d   | fifoAlt a b, ABlock c d => in_right
      | fifoAlt a b, transformTo g c d | fifoAlt a b, filterTo g c d  => in_right 
      | SBlock a b, asyncTo c d  | SBlock a b, to c d 
      | SBlock a b, fifoAlt c d   | SBlock a b, ABlock c d => in_right
      | SBlock a b, transformTo g c d | SBlock a b, filterTo g c d => in_right
      | ABlock a b, asyncTo c d  | ABlock a b, to c d 
      | ABlock a b, fifoAlt c d   | ABlock a b, SBlock c d => in_right
      | ABlock a b, transformTo g c d | ABlock a b, filterTo g c d  => in_right
      | transformTo f a b, asyncTo c d  | transformTo f a b, fifoAlt c d 
      | transformTo f a b, SBlock c d   | transformTo f a b, ABlock c d => in_right
      | transformTo f a b, to c d => in_right
      | transformTo f a b, filterTo g c d => in_right
      | filterTo f a b, asyncTo c d  | filterTo f a b, fifoAlt c d 
      | filterTo f a b, SBlock c d   | filterTo f a b, ABlock c d => in_right
      | filterTo f a b, to c d => in_right
      | filterTo f a b, transformTo g c d => in_right
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
              | syncDrain a b => [(SBlock a b)] ++ (parse t s)
              | asyncDrain a b => [(ABlock a b)] ++ (parse t s)
              | filterReo f a b => (parse(t) (s ++ [filterTo f a b]  )) 
              | transform f a b => (parse(t) (s ++ [transformTo f a b]))
              | merger a b c => (parse(t) (s ++ [(to a c); (to b c)])) (* s ++ [(mer a b c)] *)
              | replicator a b c => (parse(t) (s ++ [(to a b); (to a c)])) (*s ++ [(rep a b c)]*)
              end
    end.

  Lemma parseSoundSync: forall pi : list connector, forall s: list program, forall a b,
                    In (sync a b) pi -> In (to a b) (parse pi s).
  Proof.
  (*intros.
  split.*)
  intros. induction pi. destruct s. simpl in H2. inversion H3. inversion H3. 
  simpl. simpl in H2. destruct H3.
  - rewrite H3. Admitted.

  Program Instance dataConnector_eqdec `{EqDec name eq} `{EqDec data eq} : EqDec (dataConnector) eq :=
  {
  equiv_dec x y :=
    match x, y with
      | dataPorts a b, dataPorts c d => if a == c then if b == d then in_left 
                                        else in_right else in_right
      | fifoData a b c, fifoData d e f => if a == d then if b == e then if c == f 
                                          then in_left else in_right else in_right
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
  - intros. induction s. simpl in H2. inversion H3.
    simpl in H3. destruct equiv_dec in H3. inversion e. exists a. split.
    simpl. auto. reflexivity.
    apply IHs in H3. destruct H3. destruct H3. exists x.
    split. simpl;auto. exact H4.
  - intros. destruct H3. destruct H3. induction s. inversion H3.
    simpl in H3. destruct H3. rewrite <- H3 in H4. rewrite H4. simpl. destruct equiv_dec. reflexivity.
    congruence. apply IHs in H3. simpl. destruct equiv_dec. reflexivity. exact H3.
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
  simpl in H3. simpl. left. rewrite andb_lazy_alt in H3. 
  apply andb_true_intro. case_eq (dInSetDataConnector s2 a). intros. rewrite H4 in H3. apply IHs in H3.
  destruct H3. split. reflexivity. auto. split. reflexivity. rewrite H3. simpl. reflexivity.
  intros. rewrite H4 in H3. inversion H3.
  - intros. induction s. reflexivity. destruct H3. simpl. simpl in H3. rewrite andb_lazy_alt in H3.
  apply andb_true_intro. case_eq (dInSetDataConnector s2 a). intros. rewrite H4 in H3.
  destruct H3. destruct IHs. left. reflexivity. auto. intros. rewrite H4 in H3. inversion H3. inversion H3.
  Defined.

(*   Fixpoint subSubset (s: set (set dataConnector)) (s2 : (set (set dataConnector))) := 
    match s,s2 with
    | a::t,b::y => subset a b && subSubset t y
    | _,_ => true
    end. -> part of the bounded iteration feature *)


  (* Auxiliary function for goTo a b and dataPorts a x -> dataPorts b x *)
  Fixpoint port2port (dataSink : goMarks) (dataSource : set dataConnector) :=
  match dataSource with 
  | [] => None
  | ax::acc => match ax,dataSink with
               | dataPorts a x, goTo y b => if equiv_decb a y then (Some (dataPorts b x)) else port2port dataSink acc
               | _, _ => port2port dataSink acc
                end
  end.
  
  Fixpoint port2portTr (transformFunction : data -> data) (dataSink : goMarks) (dataSource : set dataConnector) :=
  match dataSource with 
  | [] => None
  | ax::acc => match ax,dataSink with
               | dataPorts a x, goTransform f y b => if equiv_decb a y then (Some (dataPorts b (transformFunction(x)))) 
                                            else port2portTr transformFunction dataSink acc
               | _, _ => port2portTr transformFunction dataSink acc
                end
  end.

  Fixpoint port2portFil (filterFunction : data -> bool) (dataSink : goMarks) (dataSource : set dataConnector) :=
  match dataSource with 
  | [] => None
  | ax::acc => match ax,dataSink with
               | dataPorts a x, goFilter f y b => if equiv_decb a y && (filterFunction(x)) 
                                                  then (Some (dataPorts b (x))) 
                                                  else port2portFil filterFunction dataSink acc 
               | _, _ => port2portFil filterFunction dataSink acc
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
                                            match (port2port (goTo a b)(filter(fun y : (dataConnector) => match y with
                                            | dataPorts name1 data => (equiv_decb name1 a)
                                            | _ => false 
                                            end) (t))) with
                                            | None => (fire t l acc) 
                                            | Some x => (fire t l (x::acc)) 
                                            end
                                        else fire t l acc

              | goTransform f a b => if (existsb (fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then 
              (*busco o item de dado em t e transformo pro formato adequado*)
                                            match (port2portTr f (goTransform f a b)(filter(fun x : (dataConnector) => match x with
                                            | dataPorts name1 data => (equiv_decb name1 a)
                                            | _ => false 
                                            end) (t))) with
                                            | None => (fire t l acc) 
                                            | Some x => (fire t l ((x::acc))) 
                                            end
                                        else fire t l acc
              | goFilter f a b => if (existsb (fun x : (dataConnector) => match x with
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)) then 
                                            match (port2portFil f (goFilter f a b)(filter(fun x : (dataConnector) => match x with
                                            | dataPorts name1 data => (equiv_decb name1 a)
                                            | _ => false 
                                            end) (t))) with
                                            | None => (fire t l acc) 
                                            | Some x => (fire t l ((x::acc))) 
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
                     | goTo a b => match current with
                                   | goTo u v => if (equiv_decb b v) then (goTo u v)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                   | goFifo u w v => if (equiv_decb b v) then (goFifo u w v)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                   | goFromFifo u w v => if (equiv_decb b v) then (goFromFifo u w v)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                   | goTransform f u v => if (equiv_decb b v) then (goTransform f a b)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                   | goFilter f u v => if (equiv_decb b v) then (goFilter f a b)::(swap t current) 
                                                 else (goTo a b)::(swap t current)
                                    end
                     | goTransform f a b => match current with
                                   | goTo u v => if (equiv_decb b v) then (goTo u v)::(swap t current) 
                                                 else (goTransform f a b)::(swap t current)
                                   | goFifo u w v => if (equiv_decb b v) then (goFifo u w v)::(swap t current) 
                                                 else (goTransform f a b)::(swap t current)
                                   | goFromFifo u w v => if (equiv_decb b v) then (goFromFifo u w v)::(swap t current) 
                                                 else (goTransform f a b)::(swap t current)
                                   | goTransform f u v => if (equiv_decb b v) then (goTransform f a b)::(swap t current) 
                                                 else (goTransform f a b)::(swap t current)
                                   | goFilter f' u v => if (equiv_decb b v) then (goFilter f' a b)::(swap t current) 
                                                 else (goTransform f a b)::(swap t current)
                                    end
                     | goFilter f a b => match current with
                                   | goTo u v => if (equiv_decb b v) then (goTo u v)::(swap t current) 
                                                 else (goFilter f a b)::(swap t current)
                                   | goFifo u w v => if (equiv_decb b v) then (goFifo u w v)::(swap t current) 
                                                 else (goFilter f a b)::(swap t current)
                                   | goFromFifo u w v => if (equiv_decb b v) then (goFromFifo u w v)::(swap t current) 
                                                 else (goFilter f a b)::(swap t current)
                                   | goTransform f' u v => if (equiv_decb b v) then (goTransform f' a b)::(swap t current) 
                                                 else (goFilter f a b)::(swap t current)
                                   | goFilter f u v => if (equiv_decb b v) then (goFilter f a b)::(swap t current) 
                                                 else (goFilter f a b)::(swap t current)
                                    end
                     | goFifo a data b => match current with
                                       | goTo x y => if (equiv_decb b y) then (goTo x y)::(swap t current) 
                                                 else (goFifo a data b)::(swap t current)
                                       | goFifo x y z => if (equiv_decb b z) then (goFifo x y z)::(swap t current) 
                                                 else (goFifo a data b)::(swap t current)
                                       | goFromFifo x y z => if (equiv_decb b z) then (goFromFifo x y z)::(swap t current) 
                                                 else (goFifo a data b)::(swap t current)
                                       | goTransform f y z => if (equiv_decb b z) then (goTransform f y z)::(swap t current) 
                                                 else (goFifo a data b)::(swap t current)
                                       | goFilter f u v => if (equiv_decb b v) then (goFilter f a b)::(swap t current) 
                                                 else (goFifo a data b)::(swap t current)
                                        end
                     | goFromFifo a data b => match current with
                                       | goTo x y => if (equiv_decb b y) then (goTo x y)::(swap t current) 
                                                 else (goFromFifo a data b)::(swap t current)
                                       | goFifo x y z => if (equiv_decb b z) then (goFifo x y z)::(swap t current) 
                                                 else (goFromFifo a data b)::(swap t current)
                                       | goFromFifo x y z => if (equiv_decb b z) then (goFromFifo x y z)::(swap t current) 
                                                 else (goFromFifo a data b)::(swap t current)
                                       | goTransform f y z => if (equiv_decb b z) then (goTransform f y z)::(swap t current) 
                                                 else (goFromFifo a data b)::(swap t current)
                                       | goFilter f u v => if (equiv_decb b v) then (goFilter f a b)::(swap t current) 
                                                 else (goFromFifo a data b)::(swap t current)
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
  intros. induction t. simpl in H3. inversion H3. simpl in H3. case_eq (a0). intros. rewrite H4 in H3.
  inversion H3. simpl. auto. intros. rewrite H4 in H3.
  inversion H3. simpl. auto. 
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
                                        | transformTo f name1 name2 => (nequiv_decb name1 a)
                                        | filterTo f name1 name2 => (nequiv_decb name1 a)
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
    | Datatypes.S n  =>  match s with
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
                                            | goTransform f name1 name2 => (equiv_decb name2 b)
                                            | goFilter f name1 name2 => (equiv_decb name2 b)
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
                                        end) (t)) then (*condição seguinte verifica se ja tem alguem com o mesmo sink no acc. Para o LossySync, também avaliar se tem alguém com o destino sendo o source node, uma vez que fica A para A*)
                                          if negb((existsb (fun x : goMarks => match x with
                                            | goTo name1 name2 => (equiv_decb name2 b) || (equiv_decb name2 a) 
                                            | goFifo name1 data name2 => (equiv_decb name2 b) || (equiv_decb name2 a) 
                                            | goFromFifo name1 data name2 => (equiv_decb name2 b) || (equiv_decb name2 a) 
                                            | goTransform f name1 name2 => (equiv_decb name2 b) || (equiv_decb name2 a) 
                                            | goFilter f name1 name2 => (equiv_decb name2 b) || (equiv_decb name2 a) 
                                            end) (acc))) 
                                          then (*caso 1*)
                                            (go s' n (acc++[goTo a b]) t) ++ (go s' n (acc++[goTo a a])  t)
                                         else (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                            (go s' n ((swap acc (goTo a b))++[goTo a b]) t) ++ (go s' n (acc) t)
                                      else 
                                      (go s' n acc t)
                        | transformTo f a b => if existsb (fun x : (dataConnector) => match x with (*a sync b *)
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)then (*condição seguinte verifica se ja tem alguem com o mesmo sink no acc *)
                                          if negb((existsb (fun x : goMarks => match x with
                                            | goTo name1 name2 => (equiv_decb name2 b) 
                                            | goFifo name1 data name2 => (equiv_decb name2 b)
                                            | goFromFifo name1 data name2 => (equiv_decb name2 b)
                                            | goTransform f name1 name2 => (equiv_decb name2 b)
                                            | goFilter f name1 name2 => (equiv_decb name2 b)
                                            end) (acc)))
                                         then  (*caso 1*)
                                            (go s' n (acc++[goTransform f a b]) t)
                                         else  (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                             (go s' n (swap acc (goTransform f a b)) t) ++ (go s' n (acc) t)
                                      else 
                                      (go s' n acc t)
                        | filterTo f a b => if existsb (fun x : (dataConnector) => match x with (*a sync b *)
                                        | dataPorts name1 data => (equiv_decb name1 a)
                                        | _ => false
                                        end) (t)then (*condição seguinte verifica se ja tem alguem com o mesmo sink no acc *)
                                          if negb((existsb (fun x : goMarks => match x with
                                            | goTo name1 name2 => (equiv_decb name2 b) 
                                            | goFifo name1 data name2 => (equiv_decb name2 b)
                                            | goFromFifo name1 data name2 => (equiv_decb name2 b)
                                            | goTransform f name1 name2 => (equiv_decb name2 b)
                                            | goFilter f name1 name2 => (equiv_decb name2 b)
                                            end) (acc)))
                                         then  (*caso 1*)
                                            (go s' n (acc++[goFilter f a b]) t)
                                         else  (*caso 2 - existe alguem em acc que possui o mesmo sink*)
                                             (go s' n (swap acc (goFilter f a b)) t) ++ (go s' n (acc) t)
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
                                            | goTransform f name1 name2 => (equiv_decb name2 b)
                                            | goFilter f name1 name2 => (equiv_decb name2 b)
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

Program Instance syntaticProgram_eqdec `{EqDec name eq} : EqDec syntaticProgram eq :=
  { equiv_dec x y :=
    match x, y with
      | sProgram a , sProgram b  => if a == b then in_left else in_right
      | star a, star b => if a == b then in_left else in_right 
      | sProgram a, star b | star a, sProgram b => in_right 
    end
    }.

  Notation "# pi" := (sProgram pi) (no associativity, at level 69).
  (* Notation "nu. pi" := (nu pi) (no associativity, at level 69). *)
  Notation "pi *" := (star pi) (no associativity, at level 69).

  (* We define our logic's syntax formulae based on classic modal logic's connectives *)
  Inductive formula:=
  | proposition : (*Prop*) (* nat *) (dataProp name data) -> formula
  | box : set dataConnector -> syntaticProgram -> formula -> formula
  | diamond : set dataConnector -> syntaticProgram -> formula -> formula
  | and : formula -> formula -> formula
  | or : formula -> formula -> formula
  | neg : formula -> formula
  | imp : formula -> formula -> formula
  | biImpl : formula -> formula -> formula
  | quiFormulaBox : nat -> formula -> formula
  | quiFormulaDia : nat -> formula -> formula.
  (*02/03 - BNF sintática parece ok. notação do diamond tá bugada *)

  Program Instance formula_eqDec `(eqa: EqDec name eq) `(eqb : EqDec data eq)  : EqDec (formula) eq :=
    { equiv_dec := fix rec dc1 dc2 :=
      match dc1,dc2 with
       | proposition a, proposition b => if a == b then in_left else in_right
       | box a b c, box d e f => if a == d then if b == e  then if rec c f  
                                then in_left else in_right else in_right else in_right
       | diamond a b c, diamond d e f => if a == d then if b == e  then if rec c f  
                                then in_left else in_right else in_right else in_right
       | and a b, and c d => if rec a c then if rec b d
                                then in_left else in_right else in_right
       | or a b, or c d => if rec a c then if rec b d
                                then in_left else in_right else in_right
       | imp a b, imp c d => if rec a c then if rec b d
                                then in_left else in_right else in_right
       | biImpl a b, biImpl c d => if rec a c then if rec b d
                                then in_left else in_right else in_right
       | neg a, neg b => if rec a b then in_left else in_right
       
       | quiFormulaBox x phi, quiFormulaBox y phi' => if x == y then if rec phi phi' then in_left else in_right else in_right

       | quiFormulaDia x phi, quiFormulaDia y phi' => if x == y then if rec phi phi' then in_left else in_right else in_right

       | proposition a , box b c d | proposition a , diamond b c d => in_right
       | proposition a , and b c | proposition a , or b c | proposition a , imp b c 
       | proposition a , biImpl b c => in_right
       | proposition a , neg b => in_right
       | proposition a , quiFormulaBox x phi | proposition a , quiFormulaDia x phi => in_right


       | box a b c, proposition d => in_right 
       | box a b c , diamond d e f => in_right
       | box a b c, and d e | box a b c , or d e | box a b c , imp d e 
       | box a b c , biImpl d e => in_right
       | box a b c, neg d => in_right
       | box a b c , quiFormulaBox x phi | box a b c, quiFormulaDia x phi => in_right
       | diamond a b c, proposition d => in_right 
       | diamond a b c , box d e f => in_right
       | diamond a b c, and d e | diamond a b c , or d e | diamond a b c , imp d e 
       | diamond a b c , biImpl d e => in_right
       | diamond a b c, neg d => in_right
       | diamond a b c , quiFormulaBox x phi | diamond a b c , quiFormulaDia x phi => in_right

       | or a b, proposition d => in_right 
       | or a b , box d e f => in_right
       | or a b, and c d | or a b , imp c d
       | or a b , biImpl c d => in_right
       | or a b , diamond c d e => in_right
       | or a b, neg c => in_right
       | or a b , quiFormulaBox x phi | or a b , quiFormulaDia x phi => in_right
       | and a b, proposition d => in_right 
       | and a b , box d e f => in_right
       | and a b, or c d | and a b , imp c d
       | and a b , biImpl c d => in_right
       | and a b , diamond c d e => in_right
       | and a b, neg c => in_right
       | and a b , quiFormulaBox x phi | and a b , quiFormulaDia x phi => in_right
       | imp a b, proposition d => in_right 
       | imp a b , box d e f => in_right
       | imp a b, and c d | imp a b , or c d
       | imp a b , biImpl c d => in_right
       | imp a b , diamond c d e => in_right
       | imp a b, neg c => in_right
       | imp a b , quiFormulaBox x phi | imp a b , quiFormulaDia x phi => in_right
       | biImpl a b, proposition d => in_right 
       | biImpl a b , box d e f => in_right
       | biImpl a b, and c d | biImpl a b , or c d
       | biImpl a b , imp c d => in_right
       | biImpl a b , diamond c d e => in_right
       | biImpl a b, neg c => in_right
       | biImpl a b , quiFormulaBox x phi | biImpl a b , quiFormulaDia x phi => in_right

       | neg a, proposition b => in_right 
       | neg a , box d e f => in_right
       | neg a, and c d | neg a, imp c d
       | neg a , biImpl c d => in_right
       | neg a , diamond c d e => in_right
       | neg a, or c d => in_right
       | neg a , quiFormulaBox x phi | neg a, quiFormulaDia x phi => in_right

       | quiFormulaBox x phi, proposition b => in_right 
       | quiFormulaBox x phi , box d e f => in_right
       | quiFormulaBox x phi , and c d | quiFormulaBox x phi, imp c d
       | quiFormulaBox x phi , biImpl c d => in_right
       | quiFormulaBox x phi , diamond c d e => in_right
       | quiFormulaBox x phi, or c d => in_right
       | quiFormulaBox x phi , neg a => in_right | quiFormulaBox x phi, quiFormulaDia y phi' => in_right

       | quiFormulaDia x phi, proposition b => in_right 
       | quiFormulaDia x phi , box d e f => in_right
       | quiFormulaDia x phi , and c d | quiFormulaDia x phi, imp c d
       | quiFormulaDia x phi , biImpl c d => in_right
       | quiFormulaDia x phi , diamond c d e => in_right
       | quiFormulaDia x phi, or c d => in_right
       | quiFormulaDia x phi , neg a => in_right | quiFormulaDia x phi, quiFormulaBox y phi' => in_right

      end
    }.

  Check formula_eqDec.

  Notation " < t , pi >" := (diamond t pi) (left associativity, at level 69).
  Notation " [' t , pi ']" := (box t pi) (no associativity, at level 69).

  (* We provide a proposition to state a data item of a port *)

(*   Definition dataFromPorts (data: dataConnector) :=
    match data with
    | dataPorts a x => x
    | fifoData a x b => x
    end.

  Definition dataInPort (n: dataConnector) (d:data): Prop := 
    dataFromPorts n = d. 

  Definition dataInFifoProp (n: dataConnector) (d: data) : Prop :=
    dataFromPorts n = d. *)

  (*descontinued
  Fixpoint getData (portsData : set dataConnector) (portName : name) (portData : data) : bool :=
    match portsData with 
    | a::t => match a with
              | dataPorts name data => equiv_decb data portData
              | _ => getData t portName portData
              end
    | _ => false
    end.

  Lemma getDataSound: forall portsData, forall portsName, forall portData, 
    getData portsData portsName portData = true -> exists x, exists name, exists data, 
        In (x) (portsData) /\ x = dataPorts name data /\ (equiv_decb data portData) = true.
  Proof.
  intros.
  induction portsData. intros. inversion H3.
  intros. simpl in H2. case_eq a. intros. rewrite H4 in H3. 
  apply IHportsData in H3. destruct H3. destruct H3. destruct H3.
  destruct H3. destruct H5. exists x. exists x0. exists x1.
  simpl. split. right. exact H3. split. exact H5. assumption.
  intros. rewrite H4 in H3. exists a. exists n. exists d.
  split. simpl. left. auto. auto.
  Defined. *)

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

  Definition diamondSatisfactionPi (m:model) (p : dataProp name data) 
    (states : set state) :=
    if (states == []) then false else
    existsb (fun x : state => (V(m)x p)) states.

  Definition boxSatisfactionPi (m:model) (p : dataProp name data) 
    (states: set state) :=
    if (states == []) then false else
    forallb (fun x : state => (V(m)x p)) states.

  Notation "x |> f" := (f x) (at level 79, no associativity).


  Fixpoint singleModelStep (m:model) (formula : formula) (s:state) : bool :=
    (* if (retrieveRelatedStatesFromV (R(Fr(m))) s) == [] then false else *)
    match formula with
    | quiFormulaDia x phi | quiFormulaBox x phi => false
    | proposition p => (V(m) s p)
    | neg p => negb (singleModelStep m p s) 
    | and a b => (singleModelStep m a s) && (singleModelStep m b s)
    | or a b => (singleModelStep m a s) || (singleModelStep m b s)
    | imp a b => negb (singleModelStep m a s) || (singleModelStep m b s)
    | biImpl a b => (negb (singleModelStep m a s) || (singleModelStep m b s)) &&
                    (negb (singleModelStep m b s) || (singleModelStep m a s)) 
    | box t pi p' => match pi with
                  | sProgram reo => match p' with
                                   | quiFormulaDia x phi | quiFormulaBox x phi => false
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
                                   | imp a b => (negb (forallb (singleModelStep m a)
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
                                   | quiFormulaDia x phi | quiFormulaBox x phi => false
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
                                   | imp a b => (negb (forallb (singleModelStep m a)
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
                                   | imp a b => (negb (forallb (singleModelStep m a)
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
                                   | quiFormulaDia x phi | quiFormulaBox x phi => false
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
                                   | imp a b => (negb (existsb (singleModelStep m a)
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
                                   | quiFormulaDia x phi | quiFormulaBox x phi => false
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
                                   | imp a b => (negb (existsb (singleModelStep m a)
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
                                   | imp a b => (negb (existsb (singleModelStep m a)
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

  (* The evaluation of formulas is done as follows *)

  Definition singleFormulaVerify (m : model) (p : formula) 
    (t: set dataConnector) : bool :=
    (forallb (fun x => eqb x true) (map (singleModelStep m p) (getState m t))).

  (*We formalize the logic's axioms as the inductive type "formula" *)

  (*Dynamic Logic Axioms*)

  Definition axiomK (phi: option (formula)) : option (formula) :=
    match phi with
    | Some (box t pi (imp phi' phi'')) => Some (imp (box t pi phi') (box t pi phi''))
    | _ => None
    end.

  Definition axiomAnd (phi : option (formula)) : option (formula) :=
    match phi with
    | Some (box t pi (and phi' phi'')) => Some ( and (box t pi phi') (box t pi phi''))
    | _ => None
    end.

  Definition axiomDu (phi: option (formula)) : option (formula) :=
    match phi with
    | Some (box t pi (neg phi')) => Some (neg (diamond t pi phi'))
    | Some (neg (diamond t pi phi')) => Some (box t pi (neg phi') )
    | _ => None
    end.


  Definition axiomR (phi: option (formula)) : option (formula) :=
    match phi with
    | Some (diamond t pi phi) => Some phi
    | _ => None
    end.

  Definition axiomIt (phi: option (formula)) : option (formula) :=
    match phi with
    | Some (and (phi') (box t (sProgram pi) (box t' (star pi') phi''))) => if (equiv_decb phi' phi'')(*&&
        (equiv_decb pi pi') then *) then
        Some (box t (star pi') phi') else None (*ERICK: da erro se usarmos a mesma
variavel no pattern matching em dois lugares diferentes.R: usar variaveis diferentes e forçar a ser igual.*)
    | Some (box t (star pi) phi') => Some (and (phi') (box t (sProgram pi) (box t (star pi) phi')))
    | _ => None
    end.  

  Definition axiomInd (phi: option (formula)) : option (formula) :=
    match phi with
    | Some (and (phi') (box t pi (imp (phi'') (box t' (star pi') phi''')))) => Some (box t (star pi') phi')
    | _ => None
    end.

  End LogicMain.

  Section ModelExecution.

  Variable name state data: Type.
  Context `{EqDec name eq} `{EqDec data eq} `{EqDec state eq} `{EqDec (data -> data) eq}.
  Context (hfil:`{EqDec (data -> bool) eq}).

  Obligation Tactic := congruence.
  Program Instance dataProp_eqdec2 {name data : Type} `{EqDec name eq} `{EqDec data eq} : EqDec (dataProp name data) eq :=
   {
    equiv_dec x y (* := fix rec x y *) :=
      match x, y with
        | dataInPorts a x, dataInPorts b y => if a == b then if x == y then in_left else in_right else in_right
        | dataInFifo a x b, dataInFifo c y d => if a == c then if b == d then if x == y then in_left else in_right else in_right else in_right
        | dataBothPorts _ a b, dataBothPorts _ c d => if a == c then if b == d then in_left else in_right else in_right
 (*        | quiFormulaBox x phi, quiFormulaBox y phi' => if x == y then if rec phi phi' then in_left else in_right else in_right
        | quiFormulaDia  x phi, quiFormulaDia y phi' => if x == y then if rec phi phi' then in_left else in_right else in_right *)
        | dataInPorts a x , dataInFifo b y c => in_right
        | dataInPorts a x , dataBothPorts _ b y => in_right
(*         | dataInPorts a x , quiFormulaBox y phi' => in_right
        | dataInPorts a x , quiFormulaDia y phi' => in_right *)
        | dataInFifo a x b , dataInPorts c y => in_right
        | dataInFifo a x b , dataBothPorts _ c y => in_right
(*         | dataInFifo a x b , quiFormulaBox y phi' => in_right
        | dataInFifo a x b , quiFormulaDia y phi' => in_right *)
        | dataBothPorts _ a b , dataInPorts c y => in_right
        | dataBothPorts _ a b , dataInFifo c y d  => in_right
(*         | dataBothPorts _ a b , quiFormulaBox x phi  => in_right
        | dataBothPorts _ a b , quiFormulaDia x phi  => in_right *)
(*         | quiFormulaBox x phi , dataInPorts c y => in_right
        | quiFormulaBox x phi , dataInFifo c y d  => in_right
        | quiFormulaBox x phi , dataBothPorts _ a b => in_right
        | quiFormulaBox x phi, quiFormulaDia y phi' => in_right
        | quiFormulaDia x phi , dataInPorts c y => in_right
        | quiFormulaDia x phi , dataInFifo c y d  => in_right
        | quiFormulaDia x phi, dataBothPorts _ a b => in_right
        | quiFormulaDia x phi , quiFormulaBox y phi' => in_right *)
      end
  }.
  (* A model checker for ReLo *)

  Definition emptyLambda (s : state) (n: name) := 0%Q.

  Definition emptyDelta (s : state) : set (dataConnector name data) := [].
 
  Definition emptyVal (s : state) (prop : dataProp name data) : bool := false.

  Definition emptyModel := mkmodel ( mkframe [] [] emptyLambda emptyDelta ) (emptyVal).

  Fixpoint retrieveSinglePortProp (t : set (dataConnector name data)) (index : nat) (n : name)
    : set (dataProp name data) :=
    match t with
    | [] => []
    | a::t' => match a with
               | dataPorts a x => if (n == a) then [dataInPorts n x] else retrieveSinglePortProp t' index n
               | fifoData a x b => retrieveSinglePortProp t' index n
               end
    end.

  Definition portsHaveSameData (n1 : (dataConnector name data)) (n2 : (dataConnector name data)) : set (dataProp name data) :=
    match n1,n2 with
    | dataPorts a x, dataPorts b y => if x == y then [dataBothPorts data a b] else []
    | _ , _ => []
    end.
    
  Fixpoint retrieveTwoPortsProp  (index:nat) (t: set (dataConnector name data)) 
    (n : (dataConnector name data)) : set (dataProp name data) :=
    match t with
    | [] => []
    | a::t' => portsHaveSameData a n++(retrieveTwoPortsProp index t' n)
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

(*   Definition dataInFIFO (n1 : (dataConnector name data)) (n2 : (dataConnector name data)) : Prop :=
    if (equiv_decb n1 n2) then 
      match n1,n2 with
      | fifoData a x b, fifoData c y d => dataInFifo (fifoData a x b) x
      | _, _ => False
      end
    else False. *)

  Fixpoint retrieveFIFOdataProp (index: nat) (t: set (dataConnector name data)) 
    (n : dataConnector name data) : set (dataProp name data) :=
    match t with
    | fifodata::t' => match fifodata with
                    | fifoData a x b => if (equiv_decb fifodata n) then [dataInFifo a x b]++(retrieveFIFOdataProp index t' n)
                                        else (retrieveFIFOdataProp index t' n)
                    | dataPorts a b => (retrieveFIFOdataProp index t' n)
                    end
    | [] => []
    end.

  Definition buildValidPropositions (N: set name) (index: nat) (t: set (dataConnector name data)) 
     : set (dataProp name data) :=
    ((flat_map(retrieveTwoPortsProp index t) (t))) ++ 
    (flat_map(retrieveSinglePortProp t index) (N)) ++
    (flat_map(retrieveFIFOdataProp index t) t).

  Fixpoint getProp (setProp: set (dataProp name data)) (n: (dataProp name data)) : bool :=
    match setProp with  
    | [] => false
    | a::t => if (equiv_decb a n) then true else getProp t n
    end.

   Definition getValFunctionProp (N: set name) (t:set (dataConnector name data)) (index: nat) (s:nat) (p:(dataProp name data)) :=
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
  Fixpoint getValFunction (props : set (nat * (set (dataProp name data)))) (state : nat) (prop: (dataProp name data)) :=
    match props with
    | [] => false
    | stateAndProp::moreProps => if fst(stateAndProp) == state then
                                  set_mem equiv_dec (prop) (snd(stateAndProp))
                                 else getValFunction moreProps state prop
    end.

  (* Auxiliary record to hold the global index of props*)
  Record calcProps := mkcalcProps {
    statesAndProps : set (nat * set (dataProp name data));
    propCounter : nat
  }.

  Definition getNewValFunc (calc: calcProps) (N: set name) (t:set (set (dataConnector name data))) (state: nat) :=
  mkcalcProps (set_add equiv_dec (state,flat_map (buildValidPropositions N (propCounter(calc))) t) (statesAndProps calc)) 
              (propCounter(calc) + length (flat_map (buildValidPropositions N state) t)).

   Definition addInfoToModel (m: model name nat data) (origin:nat) (dest: nat) 
    (N: set name) (t: (set (dataConnector name data))) (dataMarkups : (set (nat * (set (dataConnector name data)))))
    (calc : calcProps) :=
    mkmodel 
      (mkframe (set_add equiv_dec dest (S(Fr(m)))) (set_add equiv_dec (origin,dest) (R(Fr(m)))) (lambda(Fr(m))) 
      (getDelta dataMarkups))
      (getValFunction (statesAndProps (getNewValFunc calc N [t] dest))).

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

  (* Now a new index is allocated to the ones not visitated - Only useful to get destination states *)
  Fixpoint liftIndex (index : nat) (currentStates : set (option nat * set (dataConnector name data))) := 
    match currentStates with
    | [] => []
    | visState::moreStates => match (fst(visState)) with
                              | None => (index, (snd(visState)))::(liftIndex (Datatypes.S index) moreStates)
                              | Some a => (a,(snd(visState)))::(liftIndex index moreStates)
                              end 
    end.

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
  Fixpoint processGeneralStep (m: model name nat data) (N: set name)(visitedStates : (set (nat * (set (dataConnector name data)))))
  (calc : calcProps) (currentSetOfStates : set (nat * set (dataConnector name data)))
  (pi : (reoProgram name data)) (index : nat) :=
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
    | proposition p => m
    | quiFormulaDia x phi | quiFormulaBox x phi => m
    | diamond t' pi p => match pi with
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
    | and a b | or a b | imp a b | biImpl a b => (getModel' (getModel' m n t index a setStates calc) n t index b setStates calc)
    | neg a => (getModel' m n t index a setStates calc)
    end.

  Fixpoint getSetVisitedStates (m: model name nat data)  (n: set name) (t: set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) :=
    (*setStates : set of already visited states *)
    (*This is the new version of old "getVisitedStates"*)
    match phi with
    | proposition p => setStates
    | quiFormulaDia x phi | quiFormulaBox x phi => setStates
    | diamond t' pi p => match pi with
                        | sProgram pi' => getSetVisitedStates (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *)
                                           (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) )))) 
                                          (*calculateAmountNewStates (setStates) index*)
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        | star pi' => getSetVisitedStates (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
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
                        | sProgram pi' => getSetVisitedStates (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          ((*calculateAmountNewStates (getNewIndexesForStates t setStates index*) index) )) 
                                          n 
                                          (f(t)(program2SimpProgram (pi')))
                                          (*index begin *)
                                           (fst(snd(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
                                          (index) )))) 
                                          (*calculateAmountNewStates (setStates) index*)
                                          (*index end*)
                                          p (fst(snd(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi' index))) calc
                        | star pi' => getSetVisitedStates (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
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
    | and a b | or a b | imp a b | biImpl a b => (getSetVisitedStates (getModel' m n t index a setStates calc) n t index b setStates calc)
    | neg a => (getSetVisitedStates m n t index a setStates calc) 
    end.

  (* Below definition formalizes the iteration expansion for the model generator *)

  Fixpoint expandStarFormulas (m : model name nat data) (n : set name) (t : set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) (upperBound : nat) :=
    (*upperBound - limits the search space for \star if no satisfiable model could be found until <upperBound> iterations *)
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
                                                      expandStarFormulas (getModel' m n t index (phi) setStates calc) n t index (box t' (sProgram pi') phi) setStates calc k
                                        | star pi' => if singleModelStep (getModel' m n t index (p) setStates calc) 
                                                        (p)
                                                        (*Retrieve the state denoted by T in the model
                                                          Próximo passo, considerar que pode ter mais de um estado aqui...*) 
                                                        (getOrigin (hd [] t) setStates) then
                                                      (* singleModelStep *) 
                                                      ((getModel' m n t index (p) setStates calc),(setStates,upperBound)) else 
                                                      expandStarFormulas (getModel' m n t index (phi) setStates calc) n t index (box t' (sProgram pi') p) setStates calc k
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
                                        | star pi' => if singleModelStep (getModel' (getModel' m n t index (phi) setStates calc) n t index (p) setStates calc) 
                                                        (p)
                                                        (*Retrieve the state denoted by T in the model
                                                          Próximo passo, considerar que pode ter mais de um estado aqui...*) 
                                                        (getOrigin (hd [] t) setStates) then
                                                      (* singleModelStep *) 
                                                      ((getModel' m n t index (p) setStates calc),(setStates,upperBound)) else 
                                                      expandStarFormulas (getModel' m n t index (phi) setStates calc) n t index (diamond t' (sProgram pi') p) setStates calc k
                                         end
                       (*Acho que cláusula abaixo tem qhe chamar a getModel', ou atualizar isso na getModel.*)
                       | _ => ( m, (setStates, 0))
                       end
    end.

(* OBS: incorporar expandStarFormulas dentro de getModel talvez permita a chamada dela, ao invés de getmodel'.
  Não adianta. dá ruim *)

(*We may finally define the model generator by means of the following function, which joins the search procedure *)

Fixpoint getModel (m: model name nat data)  (n: set name) (t: set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) (upperBound : nat) :=
    (* upperBound - limits the search space for \star if no satisfiable model could be found until <upperBound> iterations *)
    (* setStates : set of already visited states *)
    (* index always start from 1 in the beggining of a run as it is the first available index for a state (0 is already for the initial *)
    (* state *)
    match phi with
    | proposition p => m
    | quiFormulaDia x phi | quiFormulaBox x phi => m
    | diamond t' pi p => match pi with
                        | sProgram pi' => getModel (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
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
                                          (*calc end*) upperBound
                        | star pi' => fst(expandStarFormulas m
                                          n 
                                          (t)
                                          (*index begin *) 
                                          (index)
                                          (*index end*)
                                          phi (setStates) 
                                          (*calc begin*) 
                                          (calc)
                                          (*calc end*) upperBound) 
                        end
    | box t' pi p => match pi with 
                        | sProgram pi' => getModel (fst(processGeneralStep m n setStates calc (getNewIndexesForStates t setStates index) pi'
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
                                          (*calc end*) upperBound
                        | star pi' => fst(expandStarFormulas m
                                          n 
                                          (t)
                                          (*index begin *) 
                                          (index)
                                          (*index end*)
                                          phi (setStates) 
                                          (*calc begin*) 
                                          (calc)
                                          (*calc end*) upperBound) 
                        end

    (*First Calcuate the model of a, followed by the model of b. might need the set of states and calc as well -not required as they
      have the same starting point.*)
    | and a b | or a b | imp a b | biImpl a b => (getModel (getModel m n t index a setStates calc upperBound) n t index b setStates calc) upperBound
    | neg a => (getModel m n t index a setStates calc upperBound)
    end.

(* And then we define the top level function that will build the model. *)
  Definition constructModel (n: set name) (t: set (set (dataConnector name data)))  
    (phi: (formula name data)) (upperBound : nat) :=
    getModel (buildPropModel n (hd [] t) 0) n t 1 phi (getNewIndexesForStates t [] 0) (mkcalcProps [] 0) upperBound.

(*Returns the calc structure of a model construction run *)
 Fixpoint getCalc (m: model name nat data) (n: set name) (t: set (set (dataConnector name data))) (index:nat)
    (phi: (formula name data)) (setStates: set (nat *  (set (dataConnector name data)))) (calc : calcProps) :=
    match phi with
    | proposition p => calc
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

  Section TableauDef.

  Variable state name data tableauFormula : Type.

  (*We define a tree structure to denote the tableau configuration*)
  Inductive binTree : Type :=
  | nilLeaf : binTree
  | leaf : (state * (((formula name data)) * bool)) -> binTree
  | node : (state * (((formula name data)) * bool)) -> binTree -> binTree -> binTree.

  (*Auxiliary tree definition with a parent relation*)
  Inductive auxBinTree : Type :=
  | auxNilLeaf : auxBinTree -> auxBinTree
  | auxLeaf : (state * (((formula name data)) * bool)) -> auxBinTree -> auxBinTree
  | auxNode : (state * (((formula name data)) * bool)) -> auxBinTree -> auxBinTree -> auxBinTree -> auxBinTree.

  
  (*A Tableau for Relo is defined as a Coq record containing the proof tree and the sequence of states it "visits"*)
  Record tableau := mkTableau {
    proofTree : binTree;
    statesTree : set (state * state) 
  }.

  End TableauDef.

  Section TableauFunc.
  (*Tableau-related functionalities.*)
  (* Tableau-related definitions has been splitted in two different modules to enable its formalization with states as
    defined by the user, as well as with states as natural numbers (useful for automating its construction *)

  Variable state name data : Type.

  (*Requierd definition for the usage of EqDec for data (if one employs nat as the data domain *)
  Program Instance nat_eqDec : EqDec (nat) eq :=
  { equiv_dec := fix rec x y :=
    match x,y with
    | 0, 0 => in_left
    | Datatypes.S n, Datatypes.S m => if rec n m then in_left else in_right
    |  0, Datatypes.S n | Datatypes.S n, 0 => in_right
    end
  }.

  Definition formula2Tableau (phi: formula name data) :=
    mkTableau (leaf (0, (phi, false))) ([]).

  (* Equality for formula usage in this section needs to be parametrized, and supplied within usage*)

  Context `(eqa: EqDec (formula name data) eq).

  Fixpoint searchBinTree (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool)) :=
  match t with
  | nilLeaf _ _ _ => false
  | leaf phi => (equiv_decb (fst(nodeContent)) (fst(phi))) && (equiv_decb (fst(snd(nodeContent))) (fst(snd(phi)))) 
                && (equiv_decb (snd(snd(nodeContent))) (snd(snd(nodeContent)))) 
  | node phi a b => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equiv_decb (fst(snd(nodeContent))) (fst(snd(phi))))
                    && (equiv_decb (snd(snd(nodeContent))) (snd(snd(nodeContent))))
                    then true
                    else searchBinTree a nodeContent || searchBinTree b nodeContent
  end.

  Fixpoint searchBinTreeNode (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool)) :=
  match t with
  | nilLeaf _ _ _ => None
  | leaf phi => if (equiv_decb (fst(nodeContent)) (fst(phi))) && (equiv_decb (fst(snd(nodeContent))) (fst(snd(phi)))) 
                && (equiv_decb (snd(snd(nodeContent))) (snd(snd(nodeContent))))
                then Some (leaf phi) else None 
  | node phi a b => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equiv_decb (fst(snd(nodeContent))) (fst(snd(phi))))
                    && (equiv_decb (snd(snd(nodeContent))) (snd(snd(nodeContent))))
                    then Some (leaf phi) 
                    else if searchBinTree a nodeContent then searchBinTreeNode a nodeContent else searchBinTreeNode b nodeContent
  end.

  (* Required in order to correctly parametrize the corresponding EqDec *)
  Definition equalForumla (f1: (formula name data)) (f2: (formula name data)) :=
    equiv_decb f1 f2.

  (*Usage by tableauRules : *)
  (*t : complete tableau *)
  (*t' : result of application of rule *)
  (*leafNode:  denotes the branch where the derivation must be applied *)
  Fixpoint addLeftToTableau (t : binTree nat name data) (t' : binTree nat name data) 
  (leafNode : nat * (((formula name data)) * bool)) : (binTree nat name data) :=
  match t with
    | nilLeaf _ _ _ => t (*se retornar t' vai duplicar a saida na raiz também*)
    | leaf phi => if (equiv_decb (fst(leafNode)) (fst(phi)))  && (equalForumla (fst(snd(leafNode))) (fst(snd(phi))))
                           && (equiv_decb (snd(snd(leafNode))) (snd(snd(phi)))) 
                  then ((node phi) t' (nilLeaf _ _ _))
                  else (leaf phi) 
    | node phi a b => (node phi) (addLeftToTableau a t' leafNode) ((addLeftToTableau b t' leafNode)) 
  end.

  (*Special case to add the branching-related rules results (the branches must be attached to the last node of the proof tree,
    but as two split leaf nodes*)
  Fixpoint addBranchLeftToTableau (t : binTree nat name data) (b1 : binTree nat name data) (b2 : binTree nat name data)
  (leafNode : nat * (((formula name data)) * bool)) : (binTree nat name data) :=
  match t with
    | nilLeaf _ _ _ => t
    | leaf phi => if (equiv_decb (fst(leafNode)) (fst(phi)))  && (equalForumla (fst(snd(leafNode))) (fst(snd(phi))))
                           && (equiv_decb (snd(snd(leafNode))) (snd(snd(phi)))) 
                  then ((node phi) (b1) (b2))
                  else (leaf phi)
    | node phi a b => ((node phi) (addBranchLeftToTableau a b1 b2 leafNode) ((addBranchLeftToTableau b b1 b2 leafNode)))
                      (* (addBranchLeftToTableau a b1 b2) *)
  end.

  Definition tableauRules 
  (t: binTree nat name data) (origT:  binTree nat name data) (statesTree : set (nat * nat)) 
  (nodeContent : nat * (((formula name data)) * bool)) 
  (state : nat) (destState : nat) (indexQuiFormulaBox : nat) (indexQuiFormulaDiamond : nat)
  (leafNode : nat * (((formula name data)) * bool))
  (*t: proof tree to have its rules applied*)
  (*t': original proof tree, a copy of t. Needed so we don't lose the original tree when decomposing it.*) :=
  match (searchBinTreeNode t nodeContent) with
  | None => (origT,statesTree)
  | Some tx =>
  match (* (proofTree(t)) *) tx with
  | nilLeaf _ _ _ => (tx, statesTree)
  | leaf phi => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                           && (equiv_decb (snd(snd(nodeContent))) (snd(snd(phi)))) then match (fst(snd(phi))) with
                | proposition p => (origT, statesTree)
                | quiFormulaBox n phi' => if negb (snd(snd(phi))) then
                                          match phi' with 
                                          | box t' pi p => match pi with
                                                           | star pi' => ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (p , false))) 
                                                                                             (node ((fst(phi)), (p , true)) 
                                                                                             (leaf ((fst(phi)), ((box t' pi) (quiFormulaBox indexQuiFormulaBox phi') , false))) (nilLeaf nat name data)) leafNode)
                                                                    , (statesTree))
                                                           | sProgram pi' => (origT, statesTree)
                                                           end
                                          | _ => (origT, statesTree)
                                          end
                                          else  (origT, statesTree)
                | quiFormulaDia n phi' => if (snd(snd(phi))) then
                                          match phi' with 
                                          | diamond t' pi p => match pi with
                                                           | star pi' => ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (p , true))) 
                                                                                             (node ((fst(phi)), (p , false)) 
                                                                                             (leaf ((fst(phi)), ((diamond t' pi) (quiFormulaDia indexQuiFormulaDiamond phi') , true))) (nilLeaf nat name data)) leafNode)
                                                                    , (statesTree))
                                                           | sProgram pi' => (origT, statesTree)
                                                           end
                                          | _ => (origT, statesTree)
                                          end
                                          else  (origT, statesTree)
                 | and phi1 phi2 => if (snd(snd(phi))) then
                                    ((addLeftToTableau (origT) ((node ((fst(phi)), (phi1 , true))  
                                                               (leaf ((fst(phi)), (phi2 , true))) (nilLeaf nat name data))) leafNode), (statesTree))
                                   else ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (phi1 , false)))
                                                                  (leaf ((fst(phi)), (phi2 , false))) leafNode), (statesTree))
                 | or phi1 phi2 => if (snd(snd(phi))) then
                                   ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (phi1 , true)))
                                                                    (leaf ((fst(phi)), (phi2 , true))) leafNode), (statesTree))
                                   else ((addLeftToTableau (origT) ((node ((fst(phi)), (phi1 , false))  
                                                               (leaf ((fst(phi)), (phi2 , false))) (nilLeaf nat name data))) leafNode), (statesTree)) (* ou colocar a regra do false aqui *)
                 | neg phi1 => if (snd(snd(phi))) then
                                   ((addLeftToTableau (origT) (leaf ((fst(phi)), (((phi1)) , false))) leafNode), (statesTree))
                                   else ((addLeftToTableau (origT) (leaf ((fst(phi)), (((phi1)) , true))) leafNode), (statesTree))
                | box t' pi p => match pi with
                                | sProgram pi' => if (snd(snd(phi))) then
                                                   ((addLeftToTableau (origT) ((leaf ((destState), (p , true)))) leafNode), (statesTree))
                                                  else ((addLeftToTableau (origT) ((leaf ((state), (p , false)))) leafNode) , 
                                                        (set_add equiv_dec ((fst(phi)), (state)) statesTree ))
                                | star pi' => if (snd(snd(phi))) then ((addLeftToTableau (origT) ((node ((fst(phi)), (p , true))
                                                 (leaf ((fst(phi)), (((box t' (sProgram pi')(box t' (star pi') p))) , true))) 
                                                                           (nilLeaf nat name data))) leafNode), (statesTree))
                                               else ((addLeftToTableau (origT) ((leaf ((fst(phi)), 
                                                    ((quiFormulaBox indexQuiFormulaBox p) , true)))) leafNode), (statesTree))
                                end
                | diamond t' pi p => match pi with
                                     | sProgram pi' => if (snd(snd(phi))) then
                                                       ((addLeftToTableau (origT) ((leaf ((state), (p , true)))) leafNode), 
                                                       (set_add equiv_dec ((fst(phi)), (state)) statesTree))
                                                     else ((addLeftToTableau (origT) ((leaf ((destState), (p , false)))) leafNode), (statesTree))
                                     | star pi' => if (snd(snd(phi))) then ((addLeftToTableau (origT) ((leaf ((fst(phi)), 
                                                    ((quiFormulaDia indexQuiFormulaDiamond p) , true)))) leafNode), (statesTree))
                                                      else ((addLeftToTableau (origT) ((node ((fst(phi)), (p , false))
                                                      (leaf ((fst(phi)), (((diamond t' (sProgram pi')(diamond t' (star pi') p))) , false))) 
                                                                                     (nilLeaf nat name data))) leafNode), (statesTree))
                                     end                 
                | imp phi1 phi2 => if (snd(snd(phi))) then
                                   ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (phi1 , false)))
                                                                    (leaf ((fst(phi)), (phi2 , true))) leafNode), (statesTree))
                                   else ((addBranchLeftToTableau (origT) ((node ((fst(phi)), (phi1 , true))  
                                                               (leaf ((fst(phi)), (phi2 , false)))) (nilLeaf nat name data)) (nilLeaf nat name data) leafNode), (statesTree)) 
                | _ => (tx, statesTree)
                end
                else (tx, statesTree) 
  | node phi x y => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                           && (equiv_decb (snd(snd(nodeContent))) (snd(snd(phi)))) then match (fst(snd(phi))) with
                | proposition p => (origT, statesTree)
                | quiFormulaBox n phi' => if negb (snd(snd(phi))) then
                                          match phi' with 
                                          | box t' pi p => match pi with
                                                           | star pi' => ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (p , false))) 
                                                                          (node ((fst(phi)), (p , true)) 
                                                                          (leaf ((fst(phi)), ((box t' pi) (quiFormulaBox indexQuiFormulaBox phi') , false))) (nilLeaf nat name data)) leafNode)
                                                                    , (statesTree))
                                                           | sProgram pi' => (origT, statesTree)
                                                           end
                                          | _ => (origT, statesTree)
                                          end
                                          else (origT, statesTree)
                | quiFormulaDia n phi' => if (snd(snd(phi))) then
                                          match phi' with 
                                          | diamond t' pi p => match pi with
                                                           | star pi' => ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (p , true))) 
                                                                                             (node ((fst(phi)), (p , false)) 
                                                                                             (leaf ((fst(phi)), ((diamond t' pi) (quiFormulaBox indexQuiFormulaDiamond phi') , true))) (nilLeaf nat name data)) leafNode)
                                                                    , (statesTree))
                                                           | sProgram pi' => (origT, statesTree)
                                                           end
                                          | _ => (origT, statesTree)
                                          end
                                          else  (origT, statesTree)
                 | and phi1 phi2 => if (snd(snd(phi))) then
                                    ((addLeftToTableau (origT) ((node ((fst(phi)), (phi1 , true))  
                                                               (leaf ((fst(phi)), (phi2 , true))) (nilLeaf nat name data))) leafNode), (statesTree))
                                   else ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (phi1 , false)))
                                                                    (leaf ((fst(phi)), (phi2 , false))) leafNode), (statesTree))
                 | or phi1 phi2 => if (snd(snd(phi))) then
                                   ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (phi1 , true)))
                                                                    (leaf ((fst(phi)), (phi2 , true))) leafNode), (statesTree))
                                   else ((addLeftToTableau (origT) ((node ((fst(phi)), (phi1 , false))  
                                                               (leaf ((fst(phi)), (phi2 , false))) (nilLeaf nat name data))) leafNode), (statesTree))
                 | neg phi1 => if (snd(snd(phi))) then
                                   ((addLeftToTableau (origT) (leaf ((fst(phi)), (((phi1)) , false))) leafNode), (statesTree))
                                   else ((addLeftToTableau (origT) (leaf ((fst(phi)), (((phi1)) , true))) leafNode), (statesTree))
                | box t' pi p => match pi with
                                | sProgram pi' => if (snd(snd(phi))) then
                                                  ((addLeftToTableau (origT) ((leaf ((destState), (p , true)))) leafNode), (statesTree))
                                                  else ((addLeftToTableau (origT) ((leaf ((state), (p , false)))) leafNode) , 
                                                       (set_add equiv_dec ((fst(phi)), (state)) statesTree))
                                | star pi' => if (snd(snd(phi))) then ((addLeftToTableau (origT) ((node ((fst(phi)), (p , true))
                                                 (leaf ((fst(phi)), (((box t' (sProgram pi')(box t' (star pi') p))) , true))) 
                                                                           (nilLeaf nat name data))) leafNode), (statesTree))
                                               else ((addLeftToTableau (origT) ((leaf ((fst(phi)), 
                                                    ((quiFormulaBox indexQuiFormulaBox p) , true)))) leafNode), (statesTree))
                                end
                | diamond t' pi p => match pi with
                                     | sProgram pi' => if (snd(snd(phi))) then
                                                       ((addLeftToTableau (origT) ((leaf ((state), (p , true)))) leafNode), 
                                                       (set_add equiv_dec ((fst(phi)), (state)) statesTree))
                                                     else ((addLeftToTableau (origT) ((leaf ((destState), (p , false)))) leafNode), (statesTree))
                                     | star pi' => if (snd(snd(phi))) then ((addLeftToTableau (origT) ((leaf ((fst(phi)), 
                                                    ((quiFormulaDia indexQuiFormulaDiamond p) , true)))) leafNode), (statesTree))
                                                      else ((addLeftToTableau (origT) ((node ((fst(phi)), (p , true))
                                                      (leaf ((fst(phi)), (((diamond t' (sProgram pi')(diamond t' (star pi') p))) , false))) 
                                                                                     (nilLeaf nat name data))) leafNode), (statesTree))
                                     end                 
                | imp phi1 phi2 => if (snd(snd(phi))) then
                                   ((addBranchLeftToTableau (origT) (leaf ((fst(phi)), (phi1 , false)))
                                                                    (leaf ((fst(phi)), (phi2 , true))) leafNode), (statesTree))
                                   else ((addBranchLeftToTableau (origT) ((node ((fst(phi)), (phi1 , true))  
                                                               (leaf ((fst(phi)), (phi2 , false)))) (nilLeaf nat name data)) (nilLeaf nat name data) leafNode), (statesTree)) 
                | _ => (tx, statesTree)
                end
                else (tx, statesTree)
    end
  end. 

  Definition applyRule (t: tableau nat name data) (nodeContent : nat * (((formula name data)) * bool)) 
    (state : nat) (destState : nat) (indexQuiFormulaBox : nat) (indexQuiFormulaDiamond : nat) (leafNode : nat * (((formula name data)) * bool)) :=
    (mkTableau (fst(tableauRules (proofTree(t)) (proofTree(t)) (statesTree(t)) nodeContent state destState indexQuiFormulaBox indexQuiFormulaDiamond leafNode)) 
              (snd(tableauRules (proofTree(t)) (proofTree(t)) (statesTree(t)) nodeContent state destState indexQuiFormulaBox indexQuiFormulaDiamond leafNode))). 

  (*We also provide functionalities to check whether a Tableau is closed *)

  Fixpoint getAllLeafNodes (t: binTree nat name data) : set (nat * (((formula name data)) * bool)):= 
  match t with
    | nilLeaf _ _ _ => []
    | leaf phi => [phi]
    | node phi a b =>  (getAllLeafNodes a) ++ (getAllLeafNodes b)
  end.

  Fixpoint getBranch (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool))
  (*nodeContent: formula in the leaf node which we want to find a contradiction*) := 
  match t with
    | nilLeaf _ _ _ => t
    | leaf phi => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                      && (equiv_decb (snd(snd(nodeContent))) (snd(snd(nodeContent)))) then (leaf phi) else (nilLeaf nat name data) 
    | node phi a b => if searchBinTree a nodeContent 
                      then (node phi (getBranch a nodeContent) (nilLeaf nat name data))
                      else getBranch b nodeContent
  end.

  (*Given a formula of a leaf node, checks whether there is a contradiction on a branch.*)
  Fixpoint isBranchContradictory'  (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool)) :=
  match t with 
    | nilLeaf _ _ _ => false
    | leaf phi => (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                      && ((equiv_decb (snd(snd(nodeContent))) (negb(snd(snd(phi))))) || 
                         ((equiv_decb (negb(snd(snd(nodeContent)))) (snd(snd(phi))))))
    | node phi a b => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                      && ((equiv_decb (snd(snd(nodeContent))) (negb(snd(snd(phi))))) || 
                         ((equiv_decb (negb(snd(snd(nodeContent)))) (snd(snd(phi))))))
                      then true else (isBranchContradictory' a nodeContent) || (isBranchContradictory' b nodeContent)
  end.

  Fixpoint retrieveContradictoryNodes  (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool)) :=
  match t with 
    | nilLeaf _ _ _ => None
    | leaf phi => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                      && ((equiv_decb (snd(snd(nodeContent))) (negb(snd(snd(phi))))) || 
                         ((equiv_decb (negb(snd(snd(nodeContent)))) (snd(snd(phi))))))
                  then Some (phi, nodeContent) else None
    | node phi a b => if (equiv_decb (fst(nodeContent)) (fst(phi)))  && (equalForumla (fst(snd(nodeContent))) (fst(snd(phi))))
                      && ((equiv_decb (snd(snd(nodeContent))) (negb(snd(snd(phi))))) || 
                         ((equiv_decb (negb(snd(snd(nodeContent)))) (snd(snd(phi))))))
                      then Some (phi, nodeContent) 
                      else if searchBinTree a nodeContent 
                      then retrieveContradictoryNodes a nodeContent else retrieveContradictoryNodes b nodeContent
  end.

  (*for simplicity, we separate the analysis of eventualities \mathcal{X_{\langle \rangle}} and 
    \mathcal{X_{\rbrack \rangle}} as follows*)

  (*We retrieve the states of nodes of the branch *)
  Fixpoint getStates (t: binTree nat name data) : set (nat) :=
    match t with
    | nilLeaf _ _ _ => []
    | leaf phi => [fst(phi)]
    | node phi a b => set_union equiv_dec (set_union equiv_dec ([fst(phi)]) (getStates a)) (getStates b)
    end.

  (*And check whether there is a state in the branch which is a copy of the state where the eventuality \mathcal{X}*)

  Fixpoint getFormulae (t : binTree nat name data) (state:nat) : set (formula name data) :=
    match t with
    | nilLeaf _ _ _ => []
    | leaf phi => if (fst(phi)) == state then [fst(snd(phi))] else []
    | node phi a b => if (fst(phi)) == state 
                      then set_union equiv_dec (set_union equiv_dec ([fst(snd(phi))]) 
                              (getFormulae a state)) (getFormulae b state) 
                      else set_union equiv_dec (getFormulae a state) (getFormulae b state)
    end. 

  Check getFormulae.

  Fixpoint checkCopyState (t : binTree nat name data) (statesFromBranch : set nat) 
  (formulaStateQui : set (formula name data) ) : bool :=
    match statesFromBranch with
    | [] => false 
    | st::moreStates => set_eq (getFormulae t st) (formulaStateQui) || (checkCopyState t moreStates formulaStateQui)
    end.

  (*Checks whether there is a branch in T with leaf node <nodeContent> which is contradictory*)
  Definition isBranchContradictory (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool)) :=
    match (fst(snd(nodeContent))) with
    | quiFormulaBox n phi | quiFormulaDia n phi => (isBranchContradictory' t nodeContent) 
                                                    || (checkCopyState t (getStates t) (getFormulae t (fst(nodeContent))))
    | _ => isBranchContradictory' t nodeContent
    end.


  Definition checkContradictoryBranch (t: binTree nat name data) (nodeContent : nat * (((formula name data)) * bool)) :=
  (*nodeContent here is the leaf node to retrive the *)
    isBranchContradictory (getBranch t nodeContent) (nodeContent).

  Definition isTableauClosed (t : (binTree nat name data)) : bool :=
    forallb (checkContradictoryBranch t) (getAllLeafNodes t).


  End TableauFunc.
(*   End ReoLogicCoq. *)

Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.  
Require Export Coq.Program.Program.
Require Export QArith.
