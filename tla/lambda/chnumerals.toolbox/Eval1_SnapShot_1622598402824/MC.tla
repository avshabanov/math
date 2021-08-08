---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259839979478000 == 
2
----

\* Constant expression definition @modelExpressionEval
const_expr_162259839979479000 == 
LSucc[LZero][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259839979479000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162259839979480000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162259839979481000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:46:39 PDT 2021 by isc
