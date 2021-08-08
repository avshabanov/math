---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259826664862000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_162259826664863000 == 
LSucc[LZero][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259826664863000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162259826664864000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162259826664865000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:44:26 PDT 2021 by isc
