
Require Import LogicMain.
Import ListNotations.

Obligation Tactic := congruence.
 
Inductive byzantineConsensus := 
	R' | B' | A | X | CR' | VR' | B | VB' | A' | P | R | Y | Z | VA' |  CA'. 

Program Instance modelPortsEqDec : EqDec byzantineConsensus eq :=
	{equiv_dec x y := 
		 match x, y with 
		| R' , R' => in_left 
		| R' , B' => in_right
		| R' , A => in_right
		| R' , X => in_right
		| R' , CR' => in_right
		| R' , VR' => in_right
		| R' , B => in_right
		| R' , VB' => in_right
		| R' , A' => in_right
		| R' , P => in_right
		| R' , R => in_right
		| R' , Y => in_right
		| R' , Z => in_right
		| R' , VA' => in_right
		| R' , CA' => in_right
		| B' , R' => in_right
		| B' , B' => in_left 
		| B' , A => in_right
		| B' , X => in_right
		| B' , CR' => in_right
		| B' , VR' => in_right
		| B' , B => in_right
		| B' , VB' => in_right
		| B' , A' => in_right
		| B' , P => in_right
		| B' , R => in_right
		| B' , Y => in_right
		| B' , Z => in_right
		| B' , VA' => in_right
		| B' , CA' => in_right
		| A , R' => in_right
		| A , B' => in_right
		| A , A => in_left 
		| A , X => in_right
		| A , CR' => in_right
		| A , VR' => in_right
		| A , B => in_right
		| A , VB' => in_right
		| A , A' => in_right
		| A , P => in_right
		| A , R => in_right
		| A , Y => in_right
		| A , Z => in_right
		| A , VA' => in_right
		| A , CA' => in_right
		| X , R' => in_right
		| X , B' => in_right
		| X , A => in_right
		| X , X => in_left 
		| X , CR' => in_right
		| X , VR' => in_right
		| X , B => in_right
		| X , VB' => in_right
		| X , A' => in_right
		| X , P => in_right
		| X , R => in_right
		| X , Y => in_right
		| X , Z => in_right
		| X , VA' => in_right
		| X , CA' => in_right
		| CR' , R' => in_right
		| CR' , B' => in_right
		| CR' , A => in_right
		| CR' , X => in_right
		| CR' , CR' => in_left 
		| CR' , VR' => in_right
		| CR' , B => in_right
		| CR' , VB' => in_right
		| CR' , A' => in_right
		| CR' , P => in_right
		| CR' , R => in_right
		| CR' , Y => in_right
		| CR' , Z => in_right
		| CR' , VA' => in_right
		| CR' , CA' => in_right
		| VR' , R' => in_right
		| VR' , B' => in_right
		| VR' , A => in_right
		| VR' , X => in_right
		| VR' , CR' => in_right
		| VR' , VR' => in_left 
		| VR' , B => in_right
		| VR' , VB' => in_right
		| VR' , A' => in_right
		| VR' , P => in_right
		| VR' , R => in_right
		| VR' , Y => in_right
		| VR' , Z => in_right
		| VR' , VA' => in_right
		| VR' , CA' => in_right
		| B , R' => in_right
		| B , B' => in_right
		| B , A => in_right
		| B , X => in_right
		| B , CR' => in_right
		| B , VR' => in_right
		| B , B => in_left 
		| B , VB' => in_right
		| B , A' => in_right
		| B , P => in_right
		| B , R => in_right
		| B , Y => in_right
		| B , Z => in_right
		| B , VA' => in_right
		| B , CA' => in_right
		| VB' , R' => in_right
		| VB' , B' => in_right
		| VB' , A => in_right
		| VB' , X => in_right
		| VB' , CR' => in_right
		| VB' , VR' => in_right
		| VB' , B => in_right
		| VB' , VB' => in_left 
		| VB' , A' => in_right
		| VB' , P => in_right
		| VB' , R => in_right
		| VB' , Y => in_right
		| VB' , Z => in_right
		| VB' , VA' => in_right
		| VB' , CA' => in_right
		| A' , R' => in_right
		| A' , B' => in_right
		| A' , A => in_right
		| A' , X => in_right
		| A' , CR' => in_right
		| A' , VR' => in_right
		| A' , B => in_right
		| A' , VB' => in_right
		| A' , A' => in_left 
		| A' , P => in_right
		| A' , R => in_right
		| A' , Y => in_right
		| A' , Z => in_right
		| A' , VA' => in_right
		| A' , CA' => in_right
		| P , R' => in_right
		| P , B' => in_right
		| P , A => in_right
		| P , X => in_right
		| P , CR' => in_right
		| P , VR' => in_right
		| P , B => in_right
		| P , VB' => in_right
		| P , A' => in_right
		| P , P => in_left 
		| P , R => in_right
		| P , Y => in_right
		| P , Z => in_right
		| P , VA' => in_right
		| P , CA' => in_right
		| R , R' => in_right
		| R , B' => in_right
		| R , A => in_right
		| R , X => in_right
		| R , CR' => in_right
		| R , VR' => in_right
		| R , B => in_right
		| R , VB' => in_right
		| R , A' => in_right
		| R , P => in_right
		| R , R => in_left 
		| R , Y => in_right
		| R , Z => in_right
		| R , VA' => in_right
		| R , CA' => in_right
		| Y , R' => in_right
		| Y , B' => in_right
		| Y , A => in_right
		| Y , X => in_right
		| Y , CR' => in_right
		| Y , VR' => in_right
		| Y , B => in_right
		| Y , VB' => in_right
		| Y , A' => in_right
		| Y , P => in_right
		| Y , R => in_right
		| Y , Y => in_left 
		| Y , Z => in_right
		| Y , VA' => in_right
		| Y , CA' => in_right
		| Z , R' => in_right
		| Z , B' => in_right
		| Z , A => in_right
		| Z , X => in_right
		| Z , CR' => in_right
		| Z , VR' => in_right
		| Z , B => in_right
		| Z , VB' => in_right
		| Z , A' => in_right
		| Z , P => in_right
		| Z , R => in_right
		| Z , Y => in_right
		| Z , Z => in_left 
		| Z , VA' => in_right
		| Z , CA' => in_right
		| VA' , R' => in_right
		| VA' , B' => in_right
		| VA' , A => in_right
		| VA' , X => in_right
		| VA' , CR' => in_right
		| VA' , VR' => in_right
		| VA' , B => in_right
		| VA' , VB' => in_right
		| VA' , A' => in_right
		| VA' , P => in_right
		| VA' , R => in_right
		| VA' , Y => in_right
		| VA' , Z => in_right
		| VA' , VA' => in_left 
		| VA' , CA' => in_right
		| CA' , R' => in_right
		| CA' , B' => in_right
		| CA' , A => in_right
		| CA' , X => in_right
		| CA' , CR' => in_right
		| CA' , VR' => in_right
		| CA' , B => in_right
		| CA' , VB' => in_right
		| CA' , A' => in_right
		| CA' , P => in_right
		| CA' , R => in_right
		| CA' , Y => in_right
		| CA' , Z => in_right
		| CA' , VA' => in_right
		| CA' , CA' => in_left 
	end
	}.

Close Scope Q_scope.

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

Definition timerProp (n : nat) := true.

Definition presetTimerProp (n: nat) :=
  match n with
  | 0 => true
  | Datatypes.S m => false
  end.

Definition timerAPProp (n : nat) :=
  match n with
  | 1 => true
  | 0 => false
  | Datatypes.S m => false
  end.

Definition timerBPProp (n:nat) :=
  match n with
  | 0 => true
  | Datatypes.S m => false
  end.

Definition timerVAProp (n:nat) :=
  match n with
  | 0 => true
  | Datatypes.S m => false
  end.

Definition BizantineConsensusFlowProgram := [flowFilter timerProp R' B'; flowSync nat B' A; flowSync nat B' X;
flowFilter timerProp X CR'; flowFilter timerProp A VR'; flowFilter timerProp B VB'; flowFilter timerBPProp A' B; 
flowFilter timerAPProp A' P; flowFilter timerProp  P R; flowSync nat R Y; flowSync nat R Z; flowFilter timerVAProp Y VA'; 
flowFilter timerProp Z CA'].

Definition BizantineConsensusBlockProgram := [flowSyncdrain A X; flowaSyncdrain VR' CR'; flowaSyncdrain VB' A;
flowaSyncdrain VA' CA'; flowSyncdrain Y Z].

Definition pi := sProgram (reoProg BizantineConsensusFlowProgram BizantineConsensusBlockProgram).

Definition piStar := star (reoProg BizantineConsensusFlowProgram BizantineConsensusBlockProgram).

Definition t := [dataPorts A' 1].

(*Property 1 - For the data to be in CA, it requires no data in any of the V's*)

 Definition property1 := Eval compute in constructModel 
  [R'; B' ; A ; X ; CR' ; VR' ; B ; VB' ; A' ; P ; R ; Y ; Z ; VA'; CA'] [t] 
  (((imp (box t piStar(proposition (dataInPorts CA' 1)))
         (box t piStar(and (and (neg(proposition (dataInPorts VA' 1))) 
                           (neg(proposition (dataInPorts VB' 1)))) 
                      (neg(proposition (dataInPorts VR' 1)))))))) 
  (length(BizantineConsensusFlowProgram) + length(BizantineConsensusBlockProgram)). 

Eval compute in property1.

Eval compute in singleFormulaVerify property1 (((imp  
                  (box t piStar(proposition (dataInPorts CA' 1)))
                  (box t piStar(and (and (neg(proposition (dataInPorts VA' 1))) (neg(proposition (dataInPorts VB' 1)))) 
                        (neg(proposition (dataInPorts VR' 1)))))))) t.

(*Property 2 - For the data to be in CA, it requires no data in any of the V's*)

Definition t' := [dataPorts A' 0].

(*  Definition property2 := Eval compute in constructModel 
  [R'; B' ; A ; X ; CR' ; VR' ; B ; VB' ; A' ; P ; R ; Y ; Z ; VA'; CA'] [t'] 
  (((imp (and(box t' piStar(proposition (dataInPorts VA' 0)))
              (box t' piStar (proposition (dataInPorts VR' 0))))
         (box t' piStar((and (neg(proposition (dataInPorts CA' 0))) 
                            (neg(proposition (dataInPorts CR' 0))))))))) 
  (length(BizantineConsensusFlowProgram) + length(BizantineConsensusBlockProgram)).  *)

Definition property2 := Eval compute in constructModel 
  [R'; B' ; A ; X ; CR' ; VR' ; B ; VB' ; A' ; P ; R ; Y ; Z ; VA'; CA'] [t'] 
  (((imp ((box t' piStar(proposition (dataInPorts VA' 0))))
         (box t' piStar((and (neg(proposition (dataInPorts CA' 0))) 
                            (neg(proposition (dataInPorts CR' 0))))))))) 
  (length(BizantineConsensusFlowProgram) + length(BizantineConsensusBlockProgram)).

Eval compute in property2.

Eval compute in singleFormulaVerify property2 (((imp ((box t' piStar(proposition (dataInPorts VA' 0))))
         (box t' piStar((and (neg(proposition (dataInPorts CA' 0))) 
                            (neg(proposition (dataInPorts CR' 0))))))))) t.

