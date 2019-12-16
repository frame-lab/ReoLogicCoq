Require Import LogicMainBackup1512.

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

Eval compute in ReoLogicCoq.fire data1 [ReoLogicCoq.goTo Q B E].
