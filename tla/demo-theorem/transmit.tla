------------------------------ MODULE transmit ------------------------------
EXTENDS Naturals

CONSTANT Data
VARIABLES val, rdy, ack

\* Sender transmits data to the Receiver
\* Each unit of data is carried in `val`

TypeInvariant   ==  /\ val \in Data
                    /\ rdy \in {0, 1}
                    /\ ack \in {0, 1}

Init            ==  /\ val \in Data
                    /\ rdy \in {0, 1}
                    /\ ack = rdy
                    
Send            ==  /\ rdy = ack
                    /\ val' \in Data
                    /\ rdy' = 1 - rdy
                    /\ UNCHANGED ack

Rcv             ==  /\ rdy # ack
                    /\ ack' = 1 - ack
                    /\ UNCHANGED {val, rdy}

Next            ==  \/ Send
                    \/ Rcv

Spec            ==  Init /\ [][Next]_{val, rdy, ack}

----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
  <1> SUFFICES ASSUME Spec
               PROVE  []TypeInvariant
    OBVIOUS
  <1> QED
============================================================================

