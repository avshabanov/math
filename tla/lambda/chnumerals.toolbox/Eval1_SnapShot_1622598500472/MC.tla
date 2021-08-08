---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259849443986000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_162259849443987000 == 
LSucc[LZero][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259849443987000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162259849443988000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162259849443989000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:48:14 PDT 2021 by isc
