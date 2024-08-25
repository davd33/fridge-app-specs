---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana, orange
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj, luk
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d, e, f
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_1724621973044314000 == 
{banana, orange}
----

\* MV CONSTANT definitions USERS
const_1724621973044315000 == 
{davd, mj, luk}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_1724621973044316000 == 
{a, b, c}
----

\* MV CONSTANT definitions MSG_IDS
const_1724621973044317000 == 
{d, e, f}
----

\* SYMMETRY definition
symm_1724621973044318000 == 
Permutations(const_1724621973044314000) \union Permutations(const_1724621973044315000) \union Permutations(const_1724621973044316000) \union Permutations(const_1724621973044317000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_1724621973044319000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MAX_OP_COUNT
const_1724621973044320000 == 
3
----

=============================================================================
\* Modification History
\* Created Sun Aug 25 23:39:33 CEST 2024 by Davd
