---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259853882498000 == 
2
----

\* Constant expression definition @modelExpressionEval
const_expr_162259853882499000 == 
LSucc[LZero][FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259853882499000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1622598538824100000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1622598538824101000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:48:58 PDT 2021 by isc
