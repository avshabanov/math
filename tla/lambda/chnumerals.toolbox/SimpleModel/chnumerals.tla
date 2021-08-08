----------------------------- MODULE chnumerals --------------------------------
EXTENDS Integers, TLC

CONSTANT Limit \* Upper bound limit, that model will be testing
ASSUME Limit \in Nat

IntRange == 0..Limit

FPlusOne == [x \in IntRange |-> IF x >= Limit THEN Limit ELSE x + 1] \* Helper function to convert Church numerals to integers
ReducerFunctions == {FPlusOne} \* this functions must all have the same domain and image set (T -> T)
ReducerArguments == IntRange \* must be in the domain of T
ChurchNumbers == [ReducerFunctions -> [ReducerArguments -> ReducerArguments]]

LZero == [f \in ReducerFunctions |-> [x \in ReducerArguments |-> x]] \* Zero numeral
LSucc == \* Successor function for generating next Church numeral
    [n \in ChurchNumbers |->
        [f \in ReducerFunctions |-> [x \in ReducerArguments |-> f[n[f][x]]] ]
    ]

VARIABLE
    step,   \* Execution step, ranging from 0 to Limit
    numeral \* Church numeral, produced on each step

TypeOK == \* At every step we'll verify that current Church numeral could be correctly converted to an integer 
    /\ step = numeral[FPlusOne][0]
    /\ PrintT(<<"Reduced Church Numeral", numeral[FPlusOne][0]>>)

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
===============================================================================
