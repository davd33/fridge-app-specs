---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana, orange
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d, e, f
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_1724602894557294000 == 
{banana, orange}
----

\* MV CONSTANT definitions MSG_IDS
const_1724602894557295000 == 
{a, b, c}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_1724602894557296000 == 
{d, e, f}
----

\* MV CONSTANT definitions USERS
const_1724602894557297000 == 
{davd, mj}
----

\* CONSTANT definitions @modelParameterConstants:3MAX_QTTY
const_1724602894557298000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:5MAX_OP_COUNT
const_1724602894557299000 == 
3
----

=============================================================================
\* Modification History
\* Created Sun Aug 25 18:21:34 CEST 2024 by Davd
