Require Import LogicMain.
Import ListNotations.

Obligation Tactic := congruence.

Context `{EqDec (nat -> nat) eq} (Hfil: `{EqDec (nat -> bool) eq}).

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

Close Scope Q_scope.

Check formula_eqDec.

Check dataProp_eqdec.

Definition lossyFifoProgram := [flowLossySync nat A B;flowFifo nat B C].

(*Test1 - LossyFifo *)

Definition t' := [dataPorts A 0].

Definition pi' := sProgram (reoProg lossyFifoProgram []).

Definition piStar := star (reoProg lossyFifoProgram []).

Definition formula1 := formula2Tableau
  (box t' pi' 
    (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)))).

Definition formula2 := {|
         proofTree :=
           leaf
             (0,
             (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)),
             true));
         statesTree := []
       |}.

Eval compute in formula1.

Eval compute in formula2.

 Program Instance dataProp_eqdec : EqDec (dataProp ports nat) eq :=
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

(*To employ the tableau, one needs to supply the equality relation defined, the proof tree and
  the specificnode content (i.e, the state, the formulae and its value in the state to apply the
  corresponding rule to the corresponding node *)  

Definition formulaApp1 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) (formula1)
    (0,
             (box [dataPorts A 0]
                (sProgram
                   (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1))), false)) 1 0 0 0 

(0,
             (box [dataPorts A 0]
                (sProgram
                   (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1))), false)).

Definition formulaApp2 := tableauRules (formula_eqDec Hfil portsEq nat_eqDec) 
  (proofTree(formula2)).

Eval compute in formulaApp1.

Definition formulaCompApp1 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
            (formulaApp1) 
               (1,
                (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1)), false)) 1 0 0 0
               (1,
                (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1)), false)).
 

Eval compute in formulaCompApp1.

Definition test2 := formula2Tableau (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1))).

Eval compute in test2.

Eval compute in applyRule (formula_eqDec Hfil portsEq nat_eqDec) (test2)
(0,
             (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)),
             false)) 0 0 0 0 (0,
             (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)),
             false)).

Definition testNoBox := formula2Tableau (imp
    (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1))) 
        (proposition (dataInPorts B 1))).

Eval compute in testNoBox.

Definition testNoBoxAppRule := applyRule (formula_eqDec Hfil portsEq nat_eqDec)  
    ((testNoBox))
(0,
             (imp
                (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)))
                (proposition (dataInPorts B 1)), false)) 0 0 0 0
(0,
             (imp
                (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1)))
                (proposition (dataInPorts B 1)), false)).

Eval compute in testNoBoxAppRule.


Definition testNoBoxAppRule2 := applyRule (formula_eqDec Hfil portsEq nat_eqDec)
testNoBoxAppRule
(0,
                (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)),
                true)) 0 0 0 0

(0, (proposition (dataInPorts B 1), false)).

Eval compute in testNoBoxAppRule.

Eval compute in testNoBoxAppRule2.

(*box tests*)
Definition formula1Star := formula2Tableau
  (diamond t' piStar 
    (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1)))).

Eval compute in formula1Star.

Eval compute in applyRule (formula_eqDec Hfil portsEq nat_eqDec)
formula1Star
(0,
             (diamond [dataPorts A 0]
                (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1))),
             false)) 0 0 0 0

(0,
             (diamond [dataPorts A 0]
                (star
                   (reoProg [flowLossySync nat A B; flowFifo nat B C]
                      []))
                (or (proposition (dataInPorts A 1))
                   (proposition (dataInPorts B 1))), false)).

Definition formula2Star := formula2Tableau
  (imp (diamond t' piStar 
    (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1))))
(diamond t' piStar 
    (or (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1))))).

Eval compute in formula2Star.

Definition formula2StarAppRule := applyRule (formula_eqDec Hfil portsEq nat_eqDec)
formula2Star (0,
             (imp
                (diamond [dataPorts A 0]
                   (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                   (or (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1))))
                (diamond [dataPorts A 0]
                   (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                   (or (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1)))), false)) 0 0 0 0
(0,
             (imp
                (diamond [dataPorts A 0]
                   (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                   (or (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1))))
                (diamond [dataPorts A 0]
                   (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                   (or (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1)))), false)).

Eval compute in formula2StarAppRule.

Definition formula2StarAppRule2 := applyRule (formula_eqDec Hfil portsEq nat_eqDec)
formula2StarAppRule (0,
                (diamond [dataPorts A 0]
                   (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                   (or (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1))), true)) 0 0 0 0
 (0,
                   (diamond [dataPorts A 0]
                      (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                      (or (proposition (dataInPorts A 1))
                         (proposition (dataInPorts B 1))), false)).

Eval compute in formula2StarAppRule2.

Variable varphi psi : formula ports nat.

Check t'.

Variable t : set (dataConnector ports nat).

(*Tableau axiom proofs*)

(**Axiom K**)
Definition axiomKTableau :=

(imp ((box [] (sProgram (reoProg [flowLossySync nat A B] []))
              (imp (proposition (dataInPorts A 1)) 
                   (proposition (dataInPorts B 1)))))

     (imp ((box [] (sProgram (reoProg [flowLossySync nat A B] [])))
          (proposition (dataInPorts A 1)))
          ((box [] (sProgram (reoProg [flowLossySync nat A B] [])))
          (proposition (dataInPorts B 1))))).

Definition formula2TableauK := formula2Tableau axiomKTableau.

Eval compute in formula2TableauK.

(*Rule application 1*)
Definition formula2TableauKApp1 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauK
 (0,
             (imp
                (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                   (imp (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1))))
                (imp
                   (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts A 1)))
                   (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts B 1)))), false)) 0 0 0 0

(0,
             (imp
                (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                   (imp (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1))))
                (imp
                   (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts A 1)))
                   (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts B 1)))), false)).

Eval compute in formula2TableauKApp1.
(*Rule Application 2*)

Definition formula2TableauKApp2 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauKApp1
  (0,
                   (imp
                      (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                         (proposition (dataInPorts A 1)))
                      (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                         (proposition (dataInPorts B 1))), false)) 0 0 0 0
(0,
                   (imp
                      (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                         (proposition (dataInPorts A 1)))
                      (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                         (proposition (dataInPorts B 1))), false)).

Eval compute in formula2TableauKApp2.

(*Rule application 3*)

Definition formula2TableauKApp3 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauKApp2
  (0,
                         (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                            (proposition (dataInPorts B 1)), false)) 1 0 0 0
  (0,
                         (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                            (proposition (dataInPorts B 1)), false)).

Eval compute in formula2TableauKApp3.

(*Rule appliaction 4*)

Definition formula2TableauKApp4 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauKApp3
  (0,
                (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                   (imp (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1))), true)) 1 1 0 0


  (1, (proposition (dataInPorts B 1), false)).

Eval compute in formula2TableauKApp4.

(*Rule application 5*)

Definition formula2TableauKApp5 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauKApp4
  (1,
                               (imp (proposition (dataInPorts A 1))
                                  (proposition (dataInPorts B 1)), true)) 1 1 0 0


  (1,
                               (imp (proposition (dataInPorts A 1))
                                  (proposition (dataInPorts B 1)), true)).

Eval compute in formula2TableauKApp5.

Definition formula2TableauKApp6 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauKApp5
  (0,
                      (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                         (proposition (dataInPorts A 1)), true)) 1 1 0 0


  (1, (proposition (dataInPorts A 1), false)).

Eval compute in formula2TableauKApp6.

(*Check whether the tableau is closed *)

Eval compute in isTableauClosed (formula_eqDec Hfil portsEq nat_eqDec) 
  (proofTree(formula2TableauKApp6)). 

(**Axiom And**)
Definition axiomAndTableauLeft := 
  (imp (and (box [] (sProgram (reoProg [flowLossySync nat A B] []))
            (proposition (dataInPorts A 1)))
            (box [] (sProgram (reoProg [flowLossySync nat A B] []))
            (proposition (dataInPorts B 1))))

        (box [] (sProgram (reoProg [flowLossySync nat A B] [])) 
        (and (proposition (dataInPorts A 1)) (proposition (dataInPorts B 1))))).

Definition formula2TableauAnd := formula2Tableau axiomAndTableauLeft.

Eval compute in formula2TableauAnd.

Definition formula2TableauAndApp1 := applyRule (formula_eqDec Hfil portsEq nat_eqDec) 
  formula2TableauAnd
  (0, (imp
          (and
          (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts A 1)))
          (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts B 1))))
          (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                   (and (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1)))), false)) 0 0 0 0
  (0,
             (imp
                (and
                   (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts A 1)))
                   (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                      (proposition (dataInPorts B 1))))
                (box [] (sProgram (reoProg [flowLossySync nat A B] []))
                   (and (proposition (dataInPorts A 1))
                      (proposition (dataInPorts B 1)))), false)).

Eval compute in formula2TableauAndApp1.


(**Axiom Ind **)

Definition axiomIndTableau' := 
  (imp (and (proposition (dataInPorts A 1))
       ((box [dataPorts A 0]
             (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                (imp (proposition (dataInPorts A 1)) 
                      (box [dataPorts A 0]
             (sProgram (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                (proposition(dataInPorts A 1)) )))))
      ((box [dataPorts A 0]
             (star (reoProg [flowLossySync nat A B; flowFifo nat B C] []))
                (proposition (dataInPorts A 1))))).

Definition axiomIndTableau := formula2Tableau axiomIndTableau'.



