---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259851709590000 == 
1
----

\* Constant expression definition @modelExpressionEval
const_expr_162259851709591000 == 
LSucc[LZero][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259851709591000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162259851709592000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162259851709593000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:48:37 PDT 2021 by isc
