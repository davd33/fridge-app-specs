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
const_17245248019501074000 == 
{banana, orange}
----

\* MV CONSTANT definitions USERS
const_17245248019501075000 == 
{davd, mj, luk}
----

\* MV CONSTANT definitions FRIDJ_IDS
const_17245248019501076000 == 
{a, b, c}
----

\* MV CONSTANT definitions MSG_IDS
const_17245248019501077000 == 
{d, e, f}
----

\* SYMMETRY definition
symm_17245248019501078000 == 
Permutations(const_17245248019501074000) \union Permutations(const_17245248019501075000) \union Permutations(const_17245248019501076000) \union Permutations(const_17245248019501077000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_17245248019501079000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:6MAX_OP_COUNT
const_17245248019501080000 == 
30
----

=============================================================================
\* Modification History
\* Created Sat Aug 24 20:40:01 CEST 2024 by Davd
