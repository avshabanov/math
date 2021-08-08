---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_1622598817541114000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_1622598817541115000 == 
LSucc[LSucc[LSucc[LZero]]][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1622598817541115000>>)
----

=============================================================================
\* Modification History
\* Created Tue Jun 01 18:53:37 PDT 2021 by isc
