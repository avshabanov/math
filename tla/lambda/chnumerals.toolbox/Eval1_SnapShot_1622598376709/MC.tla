---- MODULE MC ----
EXTENDS chnumerals, TLC

\* CONSTANT definitions @modelParameterConstants:0Limit
const_162259837467970000 == 
4
----

\* Constant expression definition @modelExpressionEval
const_expr_162259837467971000 == 
LSucc
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_162259837467971000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_162259837467972000 ==
FALSE/\numeral = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_162259837467973000 ==
FALSE/\numeral' = numeral
----
=============================================================================
\* Modification History
\* Created Tue Jun 01 18:46:14 PDT 2021 by isc
