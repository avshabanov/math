------------------------------- MODULE clock -------------------------------
EXTENDS Naturals
VARIABLE t

HCini   == t \in (1..12)
HCnxt   == t' = IF t # 12 THEN t + 1 ELSE 1
HC      == HCini /\ [HCnxt]_t
---------------------------------------------------------------------------- 
\* trivial:
\*THEOREM HCini /\ [HCnxt]_t => HCini

THEOREM HCini /\ [][HCnxt]_t => []HCini

\* Produces proof:
\*  <1> SUFFICES ASSUME HCini /\ [][HCnxt]_t
\*               PROVE  []HCini
\*    OBVIOUS
\*  <1> QED

\* Original version, wrong:
\*https://groups.google.com/g/tlaplus/c/Lp1NU8lE25Y/m/L8q6jumTBQAJ
\*THEOREM HC => []HCini
============================================================================
