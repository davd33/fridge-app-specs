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
const_172458673250328000 == 
{banana, orange}
----

\* MV CONSTANT definitions USERS
const_172458673250329000 == 
{davd, mj, luk}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_172458673250330000 == 
{a, b, c}
----

\* MV CONSTANT definitions MSG_IDS
const_172458673250331000 == 
{d, e, f}
----

\* SYMMETRY definition
symm_172458673250332000 == 
Permutations(const_172458673250328000) \union Permutations(const_172458673250329000) \union Permutations(const_172458673250330000) \union Permutations(const_172458673250331000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_172458673250333000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MAX_OP_COUNT
const_172458673250334000 == 
3
----

=============================================================================
\* Modification History
\* Created Sun Aug 25 13:52:12 CEST 2024 by Davd
