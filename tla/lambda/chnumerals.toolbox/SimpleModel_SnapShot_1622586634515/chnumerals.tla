----------------------------- MODULE chnumerals --------------------------------
EXTENDS Integers, TLC

CONSTANT Limit \* Upper bound limit, that model will be testing
ASSUME Limit \in Nat \union {0}

ZL == 0..Limit \* ZL - is a range of all ints

SFunction == {[ZL -> ZL]}
ChurchNumeral == {[[SFunction -> SFunction] -> [SFunction -> SFunction]]}

FPlusOne == [x \in ZL |-> IF x >= Limit THEN Limit ELSE x + 1] \* Helper function to convert Church numerals to integers
LZero == [s \in SFunction |-> [z \in ZL |-> z]] \* Zero numeral
LSucc == \* Successor function for generating next Church numeral
    [n \in ChurchNumeral |->
        [s \in SFunction |-> 
            [z \in ZL |-> s[n[s][z]] ]
        ]
    ]

VARIABLE
    step,   \* Execution step, ranging from 0 to Limit
    numeral \* Church numeral, produced on each step

TypeOK == \* At every step we'll verify that current Church numeral could be correctly converted to an integer 
    /\ step = numeral[FPlusOne][0]
    /\ PrintT(numeral[FPlusOne][0])

Init == \* Start with zero numeral
    /\ step = 0
    /\ numeral = LZero

SetNext == \* Try up to a "Limit" numbers
    /\ step < Limit
    /\ numeral' = LSucc[numeral]
    /\ step' = step + 1

ComputationComplete == \* Stop, when we tried "Limit" worth of numerals 
    /\ step = Limit
    /\ UNCHANGED<<step, numeral>>

Next ==
    \/ SetNext
    \/ ComputationComplete

-------------------------------------------------------------------------------
Spec        ==  Init /\ [][Next]_<<step, numeral>>


(*
LNext(L) == 
    [n \in L |->
        [s \in L |->
            [z \in L |->
                s[n[s][z]]
            ] 
        ] 
    ]
LExp(L) ==
    [n \in L |->
        [m \in L |->
            m[n]
        ]
    ]

LM ==
    \/ {0..Limit}
    \/ NatPlusOne(1)
*)

===============================================================================
