Require Import LogicMain.
Import ListNotations.

Obligation Tactic := congruence.

Inductive ports := A | B | C | D | E | F | G.

Program Instance portsEq : EqDec ports eq :=
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
 
Inductive statesLossyFifo := D_A | D_B | D_C | D_BFIFOC.

Program Instance statesLossyFifoEqDec : EqDec statesLossyFifo eq := 
	{equiv_dec x y := 
		match x, y with 
		| D_A,D_A => in_left 
		| D_B,D_B => in_left 
		| D_C,D_C => in_left 
		| D_BFIFOC,D_BFIFOC => in_left
    | D_A,D_B => in_right
		| D_A,D_C => in_right
		| D_A,D_BFIFOC => in_right
    | D_B,D_A => in_right
		| D_B,D_C => in_right
		| D_B,D_BFIFOC => in_right
    | D_C,D_A => in_right
		| D_C,D_B => in_right
    | D_C, D_BFIFOC => in_right
		| D_BFIFOC,D_A => in_right
    | D_BFIFOC,D_B => in_right
		| D_BFIFOC,D_C => in_right

		end 
	}.


Inductive statesSequencer := DA | DB | DC | DD | DE | DF | DG | D_DFIFOE | D_EFIFOF | D_FFIFOG.

Program Instance statesEqDec : EqDec statesSequencer eq := 
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

(* LossyFIFO - simplified *)

Definition lossyFifoProgram := [flowLossySync nat A B;flowFifo nat B C].

Close Scope Q_scope.

Definition deltaLossyFifo (s: statesLossyFifo) :=
  match s with
  | D_A => [dataPorts A 0;dataPorts A 1]
  | D_B => [dataPorts B 0;dataPorts B 1]
  | D_C => [dataPorts C 0;dataPorts C 1]
  | D_BFIFOC => [fifoData B 0 C; fifoData B 1 C]
  end.



(* experimental *)
Definition lambdaTest (s: statesLossyFifo) (port: ports) : QArith_base.Q := 1.

Definition lossyFifoFrame := mkframe [D_A; D_B; D_C; D_BFIFOC]
                             [(D_A,D_B); (D_B,D_BFIFOC); (D_BFIFOC, D_C)]
                             lambdaTest deltaLossyFifo.

Check lossyFifoFrame.

Definition getPropositionLossy (s: statesLossyFifo) :=
  match s with
  | D_A => [dataInPorts A 1; dataInPorts A 0]
  | D_B => [dataInPorts B 1; dataInPorts B 0]
  | D_BFIFOC => [dataInFifo A 1 B; dataInFifo A 0 B]
  | D_C => [dataInPorts B 1; dataInPorts C 0]
  end.



(* Instance nat_eqDec : EqDec nat eq := {equiv_dec x y := 
		match x, y with 
    | 0, 0 => in_left
    | Datatypes.S n, Datatypes.S m => if m == n then in_left else in_right
    | 0 , Datatypes.S n | Datatypes.S n, 0 => in_right
    end
    }.
  all : congruence. Defined.  *)

Program Instance dataProp_eqdec2 {name data : Type} `{EqDec name eq} `{EqDec data eq} : EqDec (dataProp name data) eq :=
    {
      equiv_dec x y :=
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

Eval compute in equiv_dec (dataInPorts A 1) (dataInPorts A 1).

(* 
  Eval compute in (dataProp_eqdec2 ports nat) dataInPorts A 1 == dataInPorts A 1. *)

Definition valuationLossyFifo (s: statesLossyFifo) (p : dataProp ports nat) :=
  existsb (fun x : (dataProp ports nat) => equiv_decb p x) (getPropositionLossy s).

Definition lossyFifoModel := mkmodel lossyFifoFrame valuationLossyFifo.

(* Example 1 - LossyFIFO*)

Definition t' := [dataPorts A 0].

Definition pi' := sProgram (reoProg lossyFifoProgram []).

Definition piStar := star (reoProg lossyFifoProgram []).

Eval compute in singleFormulaVerify lossyFifoModel
  (box t' pi' 
    (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)))) t'.

Eval compute in singleFormulaVerify lossyFifoModel
  (imp 
    ( box t' pi' (or (proposition (dataInPorts A 1)) 
                     (proposition (dataInPorts B 1))))
                  (neg (box t' pi' (proposition (dataInFifo B 1 C))))) t'.

(* Sequencer - Simplified*)
Definition SequencerProgram := [flowFifo nat D E; flowSync nat E A; flowFifo nat E F;
flowSync nat F B; flowFifo nat F G; flowSync nat G C; flowSync nat G D].

(* experimental *)
Definition sequencerLambda (s: statesSequencer) (port: ports) : QArith_base.Q := 1.

(* We define \delta \colon S \to T as follows.*)
Definition deltaSequencer (s:statesSequencer) :=
  match s with
  | DA => [dataPorts A 0;dataPorts A 1]
  | DB => [dataPorts B 0;dataPorts B 1]
  | DC => [dataPorts C 0;dataPorts C 1]
  | DD => [dataPorts D 0;dataPorts D 1]
  | DE => [dataPorts E 0;dataPorts E 1]
  | DF => [dataPorts F 0;dataPorts F 1]
  | DG => [dataPorts G 0;dataPorts G 1]
  | D_EFIFOF => [fifoData E 0 F; fifoData E 1 F]
  | D_FFIFOG => [fifoData F 0 G; fifoData F 1 G]
  | D_DFIFOE => [fifoData D 0 E; fifoData D 1 E]
  end.

Definition sequencerFrame := mkframe [DA;DB;DC;DD;DE;DF;DG;D_DFIFOE;D_EFIFOF;D_FFIFOG] 
                    [(DD,D_DFIFOE);(D_DFIFOE,DE);(DE,DA);(DE,D_EFIFOF);(D_EFIFOF,DF);(DF,DB);(DF,D_FFIFOG);
                      (D_FFIFOG,DG);(DG,DC);(DG,DD)] sequencerLambda deltaSequencer.

Definition getPropositionSequencer (s: statesSequencer) :=
  match s with
  | DA => [dataInPorts A 0; dataInPorts A 1]
  | DB => [dataInPorts B 0; dataInPorts B 1]
  | DC => [dataInPorts C 0; dataInPorts C 1]
  | DD => [dataInPorts D 0; dataInPorts D 1]
  | DE => [] 
  | DF => []
  | DG => []
  | D_EFIFOF => []
  | D_FFIFOG => []
  | D_DFIFOE => [] 
  end.

Definition sequencerValuation (s: statesSequencer) (p : (dataProp ports nat)) := 
  existsb (fun x : (dataProp ports nat) => equiv_decb p x) (getPropositionSequencer s).

Definition sequencerModel := mkmodel sequencerFrame sequencerValuation.

Definition pi := sProgram (reoProg SequencerProgram []).

Definition piStar' := star (reoProg SequencerProgram []).

Definition t := [dataPorts D 1].

Eval compute in singleFormulaVerify sequencerModel
(box t pi (proposition (dataInPorts B 1))) t.

(* Example 1 *)

Eval compute in singleFormulaVerify sequencerModel
      (box t pi 
        (((neg ((and (and (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)))
           (proposition (dataInPorts C 1)))))))) t.

(* Example 2 *)
Eval compute in singleFormulaVerify sequencerModel
      (imp 
          (box t piStar' (proposition (dataInPorts D 1)))
           (box t piStar' (proposition (dataInPorts C 1))))  t.


(* Model checker tests *)

Eval compute in buildValidPropositions [D] (0) t .

Definition testModel := buildPropModel ([D]) (t) (0).

Eval compute in singleFormulaVerify 
  (buildPropModel ([D]) (t) (0)) (proposition (dataInPorts D 1)) t.

Eval compute in buildValidPropositions [D] 0 t.

(* Definition constructModel (n: set name) (t: set (set (dataConnector name data)))  
    (phi: (formula name data)) :=
    getModel' (buildPropModel n (hd [] t) 0) n t 0 phi ([(0,t)]) (mkcalcProps [] 0). *)

(***new tests for model - 31/01/2021 ***)

Definition N := [A; B; C; D; E; F; G].

Definition calc : calcProps ports nat := (mkcalcProps [] 0).

Definition grete := getModel' (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi (proposition (dataInPorts D 1)))))))))) 
    (getNewIndexesForStates [t] [] 0) 
    (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0). 

Eval compute in grete.

Definition grete' := getCalc (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi (proposition (dataInPorts D 1)))))))))) (getNewIndexesForStates [t] [] 0) 
    (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0). 

Eval compute in grete'.

(* O length abaixo tá fudendo o plantão, que é o index. Se ele for zero, a origem fica subtraindo um *)
Definition grete2 := getModel' (emptyModel ports nat nat) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  ((((box t pi (proposition (dataInPorts D 1)))))) (getNewIndexesForStates [t] [] 0) 
    (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0).

Eval compute in grete2.

Eval compute in (length (getNewIndexesForStates [t] [] 0)).

Definition grete1' := getSetVisitedStates (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (box t pi(box t pi(box t pi(box t pi (proposition (dataInPorts D 1)))))) (getNewIndexesForStates [t] [] 0) 
    (mkcalcProps [] 0). (*Era emptyModel*)

Eval compute in grete1'.

Definition gretesads' := getModel (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (box t pi(box t pi(box t pi(box t pi (proposition (dataInPorts D 1)))))) (getNewIndexesForStates [t] [] 0) 
    (mkcalcProps [] 0) 0. (*Era emptyModel*)

Definition grete'' := constructModel [A ; B ; C ; D ; E ; F ; G] [t] 
    (box t pi(box t pi(box t pi(box t pi (proposition (dataInPorts D 1)))))) 0.

Eval compute in grete''.

Eval compute in gretesads'.

(*21/02/2021 - Tests with composite formula*)
(*calc não pode ser vazio - Isso leva a uma inconsistencia entre o primeiro estado visitado e o segundo.
  Não pode ser vazio nem nas execuções normais. tem que ser como abaixo sempre;*)

Eval compute in getNewValFunc (mkcalcProps [] 0)
[A ; B ; C ; D ; E ; F ; G] [t] 0.
  

Definition compGrete := getModel' (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (and (box t pi (proposition (dataInPorts D 1)))
       (box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi (proposition (dataInFifo D 1 E))))))))))) 
    (getNewIndexesForStates [t] [] 0) 
    (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0). 

Eval compute in compGrete.

Definition testCompGrete := getSetVisitedStates (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (and (box t pi (proposition (dataInPorts D 1)))
       (box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi (proposition (dataInFifo D 1 E))))))))))) 
    (getNewIndexesForStates [t] [] 0) 
    (mkcalcProps [] 0). 

Eval compute in testCompGrete.

Definition compGrete2 := getModel' (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (and (box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi (proposition (dataInPorts D 1))))))))))
       (box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi(box t pi (proposition (dataInFifo D 1 E))))))))))) 
    (getNewIndexesForStates [t] [] 0) 
    (mkcalcProps [] 0). 

Eval compute in compGrete2.

(*18/02/2021 - Tests with \star*)

Definition star1 := expandStarFormulas (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (box t piStar'((((((((proposition (dataInPorts G 1)))))))))) 
  (getNewIndexesForStates [t] [] 0) 
    (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0) 9.

Eval compute in star1.

(*O Trecho de código abaixo dá false pq o conjunto R é vazio para avaliação do RTC.*)
Eval compute in singleModelStep (getModel' (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) 
  [A ; B ; C ; D ; E ; F ; G] [t] 1 ((box t piStar'((((((((proposition (dataInPorts D 1))))))))))) 
  (getNewIndexesForStates [t] [] 0) (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0))
  ((box t piStar'((((((((proposition (dataInPorts D 1))))))))))) 0.


(*Versão atual do getmodel tá expandido cmo se fosse um pi o piStar na instrução acima. Isso vai mudar com o uso do expandStarFormulas*)

Eval compute in getCalc (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) 
  [A ; B ; C ; D ; E ; F ; G] [t] 1 (box t pi(box t piStar'((((((((proposition (dataInPorts D 1))))))))))) 
  (getNewIndexesForStates [t] [] 0) (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0).


(*13/03/2021* - getModel joins both behaviours in one definition *)

Definition constructModeltest1 := getModel (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
    (box t piStar'((((((((proposition (dataInPorts G 1))))))))))
    (getNewIndexesForStates [t] [] 0) 
    (mkcalcProps [] 0) 10.

Eval compute in constructModeltest1.

Definition constructModeltest1' := expandStarFormulas (buildPropModel [A ; B ; C ; D ; E ; F ; G] (t) 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (* (and (box t piStar'((((((((proposition (dataInPorts D 1))))))))))
       (box t piStar'((((((((proposition (dataInFifo D 1 E)))))))))))  *)
  (box t piStar'((((((((proposition (dataInPorts C 1))))))))))
    (getNewIndexesForStates [t] [] 0) 
    ((* getNewValFunc *) (mkcalcProps [] 0) (* [A ; B ; C ; D ; E ; F ; G] [t] 0 *) ) 10.

Eval compute in constructModeltest1'.

(* Definition star1 := expandStarFormulas (buildPropModel [A ; B ; C ; D ; E ; F ; G] t 0) [A ; B ; C ; D ; E ; F ; G] [t] 
  (1)
  (box t piStar'((((((((proposition (dataInPorts G 1)))))))))) 
  (getNewIndexesForStates [t] [] 0) 
    (getNewValFunc (mkcalcProps [] 0)
      [A ; B ; C ; D ; E ; F ; G] [t] 0) 9. *)

Definition star1Ok := Eval compute in constructModel [A ; B ; C ; D ; E ; F ; G] [t] 
  (box t piStar'((((((((proposition (dataInPorts E 1)))))))))) 10.

Eval compute in star1Ok.
