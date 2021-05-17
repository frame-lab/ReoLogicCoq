Require Import LogicMain.
Import ListNotations.

Obligation Tactic := congruence.

Inductive modelPortsType := 
	A | Y | B | X | I | J  | L | K | M | N | C. 
Program Instance modelPortsEqDec : EqDec modelPortsType eq :=
	{equiv_dec x y := 
		 match x, y with 
		| A , A => in_left 
		| A , Y => in_right
		| A , B => in_right
		| A , X => in_right
		| A , I => in_right
		| A , J  => in_right
		| A , L => in_right
		| A , K => in_right
		| A , M => in_right
		| A , N => in_right
		| A , C => in_right
		| Y , A => in_right
		| Y , Y => in_left 
		| Y , B => in_right
		| Y , X => in_right
		| Y , I => in_right
		| Y , J  => in_right
		| Y , L => in_right
		| Y , K => in_right
		| Y , M => in_right
		| Y , N => in_right
		| Y , C => in_right
		| B , A => in_right
		| B , Y => in_right
		| B , B => in_left 
		| B , X => in_right
		| B , I => in_right
		| B , J  => in_right
		| B , L => in_right
		| B , K => in_right
		| B , M => in_right
		| B , N => in_right
		| B , C => in_right
		| X , A => in_right
		| X , Y => in_right
		| X , B => in_right
		| X , X => in_left 
		| X , I => in_right
		| X , J  => in_right
		| X , L => in_right
		| X , K => in_right
		| X , M => in_right
		| X , N => in_right
		| X , C => in_right
		| I , A => in_right
		| I , Y => in_right
		| I , B => in_right
		| I , X => in_right
		| I , I => in_left 
		| I , J  => in_right
		| I , L => in_right
		| I , K => in_right
		| I , M => in_right
		| I , N => in_right
		| I , C => in_right
		| J  , A => in_right
		| J  , Y => in_right
		| J  , B => in_right
		| J  , X => in_right
		| J  , I => in_right
		| J  , J  => in_left 
		| J  , L => in_right
		| J  , K => in_right
		| J  , M => in_right
		| J  , N => in_right
		| J  , C => in_right
		| L , A => in_right
		| L , Y => in_right
		| L , B => in_right
		| L , X => in_right
		| L , I => in_right
		| L , J  => in_right
		| L , L => in_left 
		| L , K => in_right
		| L , M => in_right
		| L , N => in_right
		| L , C => in_right
		| K , A => in_right
		| K , Y => in_right
		| K , B => in_right
		| K , X => in_right
		| K , I => in_right
		| K , J  => in_right
		| K , L => in_right
		| K , K => in_left 
		| K , M => in_right
		| K , N => in_right
		| K , C => in_right
		| M , A => in_right
		| M , Y => in_right
		| M , B => in_right
		| M , X => in_right
		| M , I => in_right
		| M , J  => in_right
		| M , L => in_right
		| M , K => in_right
		| M , M => in_left 
		| M , N => in_right
		| M , C => in_right
		| N , A => in_right
		| N , Y => in_right
		| N , B => in_right
		| N , X => in_right
		| N , I => in_right
		| N , J  => in_right
		| N , L => in_right
		| N , K => in_right
		| N , M => in_right
		| N , N => in_left 
		| N , C => in_right
		| C , A => in_right
		| C , Y => in_right
		| C , B => in_right
		| C , X => in_right
		| C , I => in_right
		| C , J  => in_right
		| C , L => in_right
		| C , K => in_right
		| C , M => in_right
		| C , N => in_right
		| C , C => in_left 
	end
	}.
Close Scope Q_scope.

Program Instance dataProp_eqdec3 {name data : Type} `{EqDec name eq} `{EqDec data eq} : EqDec (dataProp name data) eq :=
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

Definition swap01 (n:nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | Datatypes.S o => (Datatypes.S o)
  end.

Definition SmartCitiesModelProg := [flowMerger nat A B Y; flowSync nat Y X; flowSync nat X I; flowSync nat X J; 
    flowTransform swap01 J L; flowSync nat I K; flowSync nat L M; flowFifo nat K N; flowMerger nat M N C].

Definition t := [dataPorts A 1].


Definition piStar := star (reoProg SmartCitiesModelProg []).

Definition SmartCitiesEx1 := constructModel [A ; Y ; B ; X ; I ; J ; L ; K ; M ; N ; C] [t] 
  (imp ((((proposition (dataInPorts A 1))))) 
        (and (box t piStar (((proposition (dataInPorts C 0)))))
             (box t piStar (((proposition (dataInPorts C 1))))))) (length(SmartCitiesModelProg) * 3).

Eval compute in SmartCitiesEx1.

Eval compute in singleFormulaVerify SmartCitiesEx1
        (imp ((((proposition (dataInPorts A 1))))) 
        (and (box t piStar (((proposition (dataInPorts C 0)))))
             (box t piStar (((proposition (dataInPorts C 1))))))) t.



