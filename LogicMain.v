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


(*Module ReoLogicCoq.*)
  Section ReoLogicCoq.

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
  (* Our valuation function depicts a proposition as a natural number, instead of a symbol. Its intuitive idea can
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

  (* Parsing of a Reo program \pi *)

  (* We define an inductive type for the conversion of a reo Connector to a Reo
     program by means of *parse* function *)

  Inductive program :=
    | to : name -> name -> program (* sync, replicator, merger *)
    | asyncTo : name -> name -> program (* LossySync : v0 era name ->  name -> name. não vejo necessidade disso *)
    | fifoAlt : name -> name -> program (* fifo *)
    | SBlock : name -> name -> program (* syncDrain *)
    | ABlock : name -> name -> program.  (* asyncDrain *)

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

  Fixpoint parse (pi: list connector) (s : list program) : list program := (*alternativamente : set program sem o construtor composite *)
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

  (*Lemma parseSoundSync: forall pi : list connector, forall s: list program, forall a b,
                    In (sync a b) pi -> In (to a b) (parse pi s).
  Proof.
  (*intros.
  split.*)
  intros. induction pi. simpl in H2. inversion H2. inversion H2. 
  rewrite H3. simpl. Search app. unfold parse.
     *)

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
  
  all:congruence.
  Defined.

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
  Qed.
 
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
  simpl in H2. simpl. left. Search andb. rewrite andb_lazy_alt in H2. 
  apply andb_true_intro. case_eq (dInSetDataConnector s2 a). intros. rewrite H3 in H2. apply IHs in H2.
  destruct H2. split. reflexivity. auto. split. reflexivity. rewrite H2. simpl. reflexivity.
  intros. rewrite H3 in H2. inversion H2.
  - intros. induction s. reflexivity. destruct H2. simpl. simpl in H2. rewrite andb_lazy_alt in H2.
  apply andb_true_intro. case_eq (dInSetDataConnector s2 a). intros. rewrite H3 in H2.
  destruct H2. destruct IHs. left. reflexivity. auto. intros. rewrite H3 in H2. inversion H2. inversion H2.
  Qed.

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

  Lemma dataConnecetorToGoMarksFifo : forall t : set dataConnector, forall a, forall b, forall x, 
    dataConnectorToGoMarksFifo t = [goFromFifo a x b] -> In (fifoData a x b) t.
  Proof.
  (*intros.
  split .
  - *)intros. induction t. simpl in H2. inversion H2. simpl in H2. case_eq (a0). intros. rewrite H3 in H2.
  inversion H2. simpl. auto. intros. rewrite H3 in H2.
  inversion H2. simpl. auto. 
  Qed.

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

  (* s': program to be iterated *)
  (* s'' : programs to be removed (given the nonsatisfied blocks) *)
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
    (*obs2: não estou checando se, por exemplo, (a -> b) \nsucc s). Deixarei isso a cargo de parse
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
  Definition f (t: set dataConnector) (pi: set connector) : set dataConnector := go t (parse pi []) (length pi) [].

  (* We define the computation of iterations bounded by repetition as follows. *)
  (* It returns the data flow of the connector which immediately preceeds a flow which have already happened.*)

  Definition boundedIteration : set dataConnector ->  set connector -> nat -> (*set dataConnector -> *)
    set (set dataConnector) -> (*set*) (set dataConnector)  :=
    fix rec t pi iterations (*acc*) resp :=
      match iterations with
      | 0 => last resp t (*as of 02-05-20, toda ocorrencia de last resp t era [last resp t] *)
      | Datatypes.S n => if existsb (subset t) resp
                         then (last resp t) 
                         else (rec (f t pi) pi n (resp ++ [t]))
                          (*set_add equiv_dec t resp)*)
      end.

  (** Syntatic definitions **)
  (* We formalize syntatic programs as pi and its operators *)
  (* sProgram stands for simple program *)

  Inductive syntaticProgram :=
  | sProgram : set connector -> syntaticProgram
  | nu : set connector -> syntaticProgram
  | star : set connector -> syntaticProgram.

  Notation "# pi" := (sProgram pi) (no associativity, at level 69).
  Notation "nu. pi" := (nu pi) (no associativity, at level 69).
  Notation "pi *" := (star pi) (no associativity, at level 69).

  (* We formalize the notion of modalities *)
  (*
  Inductive atomicFormula :=
  | proposition : (*Prop*) nat -> atomicFormula
  | box : set dataConnector -> syntaticProgram -> atomicFormula -> atomicFormula
  | diamond : set dataConnector -> syntaticProgram -> atomicFormula -> atomicFormula.
  (*11-05 A modalidade tem que aceitar fórmulas moleculares. A solução talvez seja por a modalidade
    junto de atomicFormula *) *)

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


  Notation " < t , pi >" := (diamond t pi) (left associativity, at level 69).
  Notation " [ t , pi ]" := (box t pi) (no associativity, at level 69).

  Variable pi : syntaticProgram.
  Variable t : set dataConnector.

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
    | nil => nil (*erick: posso ter mais de um estado inicial?*)
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

  Definition getTransitive (m : model) := (*flat_map (getTransitiveAux' (R(Fr(m))) (length (R(Fr(m))))) (S(Fr(m))).*)
    getTransitiveAux (S(Fr(m))) (R(Fr(m))). 

  Definition RTC (m:model) : set (state * state) :=
   set_union equiv_dec (R(Fr(m))) (set_union equiv_dec (getTransitive m) (getReflexive m)).

  (*We recover the states reached by means of \nu.pi *)

  Definition getNuPiReachedState (m:model) (t: set dataConnector) (reoConnector: set connector) :=
    getState (m) (boundedIteration t reoConnector (length reoConnector) []).


  (* The notion of diamond and box satisfaction is defined as follows (for a single modality) *)

  Definition diamondSatisfactionPi (m:model)(p : (*Prop*)nat) 
    (states : set state) :=
    existsb (fun x : state => (V(m)x p)) states.

  Definition boxSatisfactionPi (m:model) (*s:state*) (p : (*Prop*) nat) 
    (states: set state) :=
    forallb (fun x : state => (V(m)x p)) states.

  Notation "x |> f" := (f x) (at level 79, no associativity).

  (* As we have the state, we need to verify whether it is valid in the model. *)
  (* ideia: juntar evaluateFormulas em singleModelStep. qualquer coisa, dar
  rollback pro que ta no git das definições de formula e atomicFormula *)
  (* 12-05: a linguagem deve permitir que possamos modelar modalidades e fórmulas de forma
    que formulas não sejam só atomicas, combinando-as com e/ou sem *)

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
                  (* TODO testar p nu.pi*)
                  | nu reo => match p' with
                                   | proposition p'' => 
                                       boxSatisfactionPi (m) (p'')
                                       (getNuPiReachedState m t reo)
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                         (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m t reo))
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                         (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m t reo))
                                   | and a b => (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo))) &&
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | or a b => (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo))) ||
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | neg a => negb (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | impl a b => (negb (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) ||
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | biImpl a b => ((negb (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) ||
                                                (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) &&
                                                   ((negb (forallb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) ||
                                                (forallb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo))))
                                 end
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
                  (* TODO testar p nu.pi*)
                  | nu reo => match p' with
                                   | proposition p'' => 
                                       diamondSatisfactionPi (m) (p'')
                                       (getNuPiReachedState m t reo)
                                   | box t' pi' p'' => forallb (singleModelStep m p')
                                          (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m t reo))
                                   | diamond t' pi' p'' => existsb (singleModelStep m p')
                                          (flat_map (retrieveRelatedStatesFromV (RTC(m))) 
                                                    (getNuPiReachedState m t reo))
                                   | and a b => (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo))) &&
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | or a b => (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo))) ||
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | neg a => negb (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | impl a b => (negb (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) ||
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))
                                   | biImpl a b => ((negb (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) ||
                                                (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) &&
                                                   ((negb (existsb (singleModelStep m b)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo)))) ||
                                                (existsb (singleModelStep m a)
                                           (flat_map (retrieveRelatedStatesFromV (R(Fr(m)))) 
                                                    (getNuPiReachedState m t reo))))
                                   end
                  end
      end.

  Lemma singleModelStepSound_1 : forall m, forall n, forall phi, forall s, 
   phi = proposition n /\ (V(m) s n) = true -> singleModelStep m phi s = true.
  Proof.
  intros. destruct H2. rewrite H2. simpl. exact H3.
  Qed.
  



  (* The evaluation of an atomic formula is done as follows *)

  Definition singleFormulaVerify (m : model) (p : formula) 
    (t: set dataConnector) : bool :=
    (forallb (fun x => eqb x true) (map (singleModelStep m p) (getState m t))).


  (* Then we evaluate composite formulae *)
  (* segundo a função acima, ela deixa de ser necessária 
  Fixpoint evaluateFormulas (m:model) (phi : formula) (t: set dataConnector):=
    match phi with
    | atomic p => singleFormulaVerify m p t
    | and a b => evaluateFormulas m a t && evaluateFormulas m b t
    | or a b => evaluateFormulas m a t || evaluateFormulas m b t
    | neg a => negb (evaluateFormulas m a t)
    | impl a b => (negb (evaluateFormulas m a t)) || (evaluateFormulas m b t)
    | biImpl a b => ((negb (evaluateFormulas m a t)) || (evaluateFormulas m b t)) && 
                    ((negb (evaluateFormulas m b t)) || (evaluateFormulas m a t))
    end.
    *)

  (*We formalize the logic's axioms as the inductive type "formula" *)

  (*ERICK: pergunto se phi e psi devem ser fórmulas atomicas. p mim, não. *)
  (*Definition axiomK : forall t : set dataConnector, forall pi: syntaticProgram, 
                      forall phi: (*atomicFormula*) formula,forall psi: (*atomicFormula*) formula,
  (*Outra: [t,pi] (phi -> psi) -> ([t,pi] phi -> [t,pi] psi) usa nosso impl ou o -> do coq (no caso, a seta do meio?) *)
     ([t,pi] (impl ((*proposition*) phi) ((*proposition*) psi))) ->
           (impl ([t,pi] phi) ([t,pi] psi)) = True. *)

  (*End ReoLogicCoq.*)
End ReoLogicCoq.

Require Export ListSet.
Require Export List.
Require Export Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export QArith.
