Require Import LogicMain.

Inductive sequencerPorts := A | B | C | D | E | F | G.

Instance sequencerPortsEq : EqDec sequencerPorts eq :=
	{equiv_dec x y := 
		match x, y with 
		| A,A => in_left 
		| B,B => in_left 
		| C,C => in_left 
		| D,D => in_left 
		| E,E => in_left 
		| F,F => in_left 
		| G,G => in_left 
		| A,B => in_right 
		| A,C => in_right 
		| A,D => in_right 
		| A,E => in_right 
		| A,F => in_right 
		| A,G => in_right 
		| B,A => in_right 
		| B,C => in_right 
		| B,D => in_right 
		| B,E => in_right 
		| B,F => in_right 
		| B,G => in_right 
		| C,A => in_right 
		| C,B => in_right 
		| C,D => in_right 
		| C,E => in_right 
		| C,F => in_right 
		| C,G => in_right 
		| D,A => in_right 
		| D,B => in_right 
		| D,C => in_right 
		| D,E => in_right 
		| D,F => in_right 
		| D,G => in_right 
		| E,A => in_right 
		| E,B => in_right 
		| E,C => in_right 
		| E,D => in_right 
		| E,F => in_right 
		| E,G => in_right 
		| F,A => in_right 
		| F,B => in_right 
		| F,C => in_right 
		| F,D => in_right 
		| F,E => in_right 
		| F,G => in_right 
		| G,A => in_right 
		| G,B => in_right 
		| G,C => in_right 
		| G,D => in_right 
		| G,E => in_right 
		| G,F => in_right 
		end 
	}.
  Proof.
  all:congruence.
  Defined.

Definition program1 := [ReoLogicCoq.sync A B; ReoLogicCoq.sync B E; ReoLogicCoq.sync B C; ReoLogicCoq.sync C D; ReoLogicCoq.sync D A].
Definition processed1 := ReoLogicCoq.g program1 [].

Eval compute in processed1.

Eval compute in length processed1.

Definition data1 := [ReoLogicCoq.dataPorts B 1].

Eval compute in ReoLogicCoq.go data1 processed1 (length processed1) [].

Eval compute in ReoLogicCoq.fire data1 [ReoLogicCoq.goTo nat B E].


(* new tests - 12/04 *)

Inductive statesSequencer := DA | DB | DC | DD | DE | DF | DG | D_DFIFOE | D_EFIFOF | D_FFIFOG.

Instance statesEqDec : EqDec statesSequencer eq := 
	{equiv_dec x y := 
		match x, y with 
		| DA,DA => in_left 
		| DB,DB => in_left 
    | DD,DD => in_left
		| DC,DC => in_left 
		| DE,DE => in_left 
		| DF,DF => in_left 
		| DG,DG => in_left 
		| D_DFIFOE,D_DFIFOE => in_left 
		| D_EFIFOF,D_EFIFOF => in_left 
		| D_FFIFOG,D_FFIFOG => in_left 
		| DA,DB => in_right 
		| DA,DC => in_right 
    | DA,DD => in_right
		| DA,DE => in_right 
		| DA,DF => in_right 
		| DA,DG => in_right 
		| DA,D_DFIFOE => in_right 
		| DA,D_EFIFOF => in_right 
		| DA,D_FFIFOG => in_right 
		| DB,DA => in_right 
		| DB,DC => in_right 
    | DB,DD => in_right
		| DB,DE => in_right 
		| DB,DF => in_right 
		| DB,DG => in_right 
		| DB,D_DFIFOE => in_right 
		| DB,D_EFIFOF => in_right 
		| DB,D_FFIFOG => in_right 
		| DC,DA => in_right 
		| DC,DB => in_right
    | DC,DD => in_right 
		| DC,DE => in_right 
		| DC,DF => in_right 
		| DC,DG => in_right 
		| DC,D_DFIFOE => in_right 
		| DC,D_EFIFOF => in_right 
		| DC,D_FFIFOG => in_right 
		| DE,DA => in_right 
		| DE,DB => in_right 
    | DE,DD => in_right
		| DE,DC => in_right 
		| DE,DF => in_right 
		| DE,DG => in_right 
		| DE,D_DFIFOE => in_right 
		| DE,D_EFIFOF => in_right 
		| DE,D_FFIFOG => in_right 
		| DF,DA => in_right 
		| DF,DB => in_right 
    | DF,DD => in_right
		| DF,DC => in_right 
		| DF,DE => in_right 
		| DF,DG => in_right 
		| DF,D_DFIFOE => in_right 
		| DF,D_EFIFOF => in_right 
		| DF,D_FFIFOG => in_right 
		| DG,DA => in_right 
		| DG,DB => in_right 
		| DG,DC => in_right 
    | DG,DD => in_right
		| DG,DE => in_right 
		| DG,DF => in_right 
		| DG,D_DFIFOE => in_right 
		| DG,D_EFIFOF => in_right 
		| DG,D_FFIFOG => in_right 
		| D_DFIFOE,DA => in_right 
		| D_DFIFOE,DB => in_right 
		| D_DFIFOE,DC => in_right 
		| D_DFIFOE,DD => in_right 
		| D_DFIFOE,DE => in_right 
		| D_DFIFOE,DF => in_right 
		| D_DFIFOE,DG => in_right 
		| D_DFIFOE,D_EFIFOF => in_right 
		| D_DFIFOE,D_FFIFOG => in_right 
		| D_EFIFOF,DA => in_right 
		| D_EFIFOF,DB => in_right 
		| D_EFIFOF,DC => in_right 
		| D_EFIFOF,DD => in_right 
		| D_EFIFOF,DE => in_right 
		| D_EFIFOF,DF => in_right 
		| D_EFIFOF,DG => in_right 
		| D_EFIFOF,D_DFIFOE => in_right 
		| D_EFIFOF,D_FFIFOG => in_right 
		| D_FFIFOG,DA => in_right 
		| D_FFIFOG,DB => in_right 
		| D_FFIFOG,DC => in_right 
		| D_FFIFOG,DD => in_right 
		| D_FFIFOG,DE => in_right 
		| D_FFIFOG,DF => in_right 
		| D_FFIFOG,DG => in_right 
		| D_FFIFOG,D_DFIFOE => in_right 
		| D_FFIFOG,D_EFIFOF => in_right
    | DD,DA => in_right
    | DD,DB => in_right 
		| DD,DC => in_right 
		| DD,DE => in_right 
		| DD,DF => in_right 
		| DD,DG => in_right 
		| DD,D_DFIFOE => in_right 
		| DD,D_EFIFOF => in_right 
		| DD,D_FFIFOG => in_right  
		end 
	}.
Proof.
all:congruence.
Defined.

(* Record frame := mkframe {
    S : set state;
    R : set (state * state);
    lambda : state -> name -> QArith_base.Q;
    delta : state -> set dataConnector
  }.

  Close Scope Q_scope.

  (* Model definition *)
  Record model := mkmodel {
    Fr  : frame;
    V : state -> set bool*)
(* We define the Sequencer connector *)
Definition SequencerProgram := [ReoLogicCoq.fifo D E; ReoLogicCoq.sync E A; ReoLogicCoq.fifo E F;
ReoLogicCoq.sync F B; ReoLogicCoq.sync F G; ReoLogicCoq.fifo G C; ReoLogicCoq.sync G A].

(* experimental *)
Definition lambdaTest (s: statesSequencer) (port: sequencerPorts) : QArith_base.Q := 1.

Definition deltaSequencer (s:statesSequencer) :=
  match s with
  | DA => [ReoLogicCoq.dataPorts A 0;ReoLogicCoq.dataPorts A 1]
  | DB => [ReoLogicCoq.dataPorts B 0;ReoLogicCoq.dataPorts B 1]
  | DC => [ReoLogicCoq.dataPorts C 0;ReoLogicCoq.dataPorts C 1]
  | DD => [ReoLogicCoq.dataPorts D 0;ReoLogicCoq.dataPorts D 1]
  | DE => [ReoLogicCoq.dataPorts E 0;ReoLogicCoq.dataPorts E 1]
  | DF => [ReoLogicCoq.dataPorts F 0;ReoLogicCoq.dataPorts F 1]
  | DG => [ReoLogicCoq.dataPorts G 0;ReoLogicCoq.dataPorts G 1]
  | D_EFIFOF => [ReoLogicCoq.fifoData E 0 F;ReoLogicCoq.fifoData E 1 F]
  | D_FFIFOG => [ReoLogicCoq.fifoData F 0 G;ReoLogicCoq.fifoData F 1 G]
  | D_DFIFOE => [ReoLogicCoq.fifoData D 0 E;ReoLogicCoq.fifoData D 1 E]
  end.

Definition frame1 := ReoLogicCoq.mkframe [DA;DB;DC;DD;DE;DF;DG;D_DFIFOE;D_EFIFOF;D_FFIFOG] 
                    [(DD,D_DFIFOE);(D_DFIFOE,DE);(DE,DA);(DE,D_EFIFOF);(D_EFIFOF,DF);(DF,DB);(DF,D_FFIFOG);
                      (D_FFIFOG,DG);(DG,DD)] lambdaTest deltaSequencer.

Definition valuationTest (s: statesSequencer) (p : Prop) := false.

Definition model1 := ReoLogicCoq.mkmodel frame1 valuationTest.

Definition pi := ReoLogicCoq.sProgram SequencerProgram.

Definition t := [ReoLogicCoq.dataPorts D 1].


Eval compute in ReoLogicCoq.singleFormulaVerify model1 
( ReoLogicCoq.box t pi (ReoLogicCoq.diamond t pi 
    (ReoLogicCoq.proposition sequencerPorts nat True))) t.

Eval compute in ReoLogicCoq.singleFormulaVerify model1 
( ReoLogicCoq.box t pi (ReoLogicCoq.proposition sequencerPorts nat True)) t.

Eval compute in ReoLogicCoq.RTC model1.

