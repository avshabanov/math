---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259825203854000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_162259825203855000 == 
LZero[FPlusOne][0]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259825203855000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162259825203856000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162259825203857000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:44:12 PDT 2021 by isc
