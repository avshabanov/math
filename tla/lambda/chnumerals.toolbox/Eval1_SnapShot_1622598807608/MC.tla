---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_1622598805592108000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_1622598805592109000 == 
LSucc[LSucc[LZero]][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1622598805592109000>>)
----

=============================================================================
\* Modification History
\* Created Tue Jun 01 18:53:25 PDT 2021 by isc
