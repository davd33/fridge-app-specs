---- MODULE MC ----
EXTENDS FridjappImpl, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
banana
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
davd, mj
----

\* MV CONSTANT definitions INGREDIENT_TYPES
const_172286273743177000 == 
{banana}
----

\* MV CONSTANT definitions USERS
const_172286273743178000 == 
{davd, mj}
----

\* SYMMETRY definition
symm_172286273743179000 == 
Permutations(const_172286273743178000)
----

\* CONSTANT definitions @modelParameterConstants:1MAX_QTTY
const_172286273743180000 == 
3
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_172286273743181000 ==
0..1000
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_172286273743182000 ==
/\ Cardinality(AllIds) < 100
/\ \A u \in USERS: Len(msgs[u]) < 10
----
=============================================================================
\* Modification History
\* Created Mon Aug 05 14:58:57 CEST 2024 by davd33
