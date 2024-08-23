---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana, orange
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d, e
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_17243997253111174000 == 
{banana, orange}
----

\* MV CONSTANT definitions USERS
const_17243997253111175000 == 
{davd, mj}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_17243997253111176000 == 
{a, b}
----

\* MV CONSTANT definitions MSG_IDS
const_17243997253111177000 == 
{d, e}
----

\* SYMMETRY definition
symm_17243997253111178000 == 
Permutations(const_17243997253111174000) \union Permutations(const_17243997253111175000) \union Permutations(const_17243997253111176000) \union Permutations(const_17243997253111177000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_17243997253111179000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MAX_OP_COUNT
const_17243997253111180000 == 
3
----

=============================================================================
\* Modification History
\* Created Fri Aug 23 09:55:25 CEST 2024 by Davd
