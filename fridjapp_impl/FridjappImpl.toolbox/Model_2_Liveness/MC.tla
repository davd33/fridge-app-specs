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
davd, mj, luk
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_1724504225828221000 == 
{banana, orange}
----

\* MV CONSTANT definitions MSG_IDS
const_1724504225828222000 == 
{a, b, c}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_1724504225828223000 == 
{d, e, f}
----

\* MV CONSTANT definitions USERS
const_1724504225828224000 == 
{davd, mj, luk}
----

\* CONSTANT definitions @modelParameterConstants:3MAX_QTTY
const_1724504225828225000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:5MAX_OP_COUNT
const_1724504225828226000 == 
30
----

=============================================================================
\* Modification History
\* Created Sat Aug 24 14:57:05 CEST 2024 by Davd
