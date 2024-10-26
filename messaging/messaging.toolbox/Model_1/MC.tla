---- MODULE MC ----
EXTENDS messaging, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions DEVICES
const_1729984199817806000 == 
{d1, d2, d3}
----

\* SYMMETRY definition
symm_1729984199817807000 == 
Permutations(const_1729984199817806000)
----

\* CONSTANT definitions @modelParameterConstants:1DATA
const_1729984199817808000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2LEAD
const_1729984199817809000 == 
d1
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1729984199817810000 ==
1
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1729984199817811000 ==
LattestVersion < 4
----
=============================================================================
\* Modification History
\* Created Sun Oct 27 01:09:59 CEST 2024 by davd33
