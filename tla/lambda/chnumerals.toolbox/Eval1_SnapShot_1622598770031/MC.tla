---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_1622598768011104000 == 
2
----

\* Constant expression definition @modelExpressionEval
const_expr_1622598768012105000 == 
LSucc[LZero][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1622598768012105000>>)
----

=============================================================================
\* Modification History
\* Created Tue Jun 01 18:52:48 PDT 2021 by isc
