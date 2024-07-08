# Refinement Featherweight Java

## Structure
src/RFJ: the main Coq development, whose structure is outlined in Section 6.1 of the paper. 
src/Lists: some definitions and lemmas about Lists. 
src/Utils: some utils, mainly providing the Referable typeclass. 
src/Tactics: some tactics, mainly providing the crush tactic. 

### Main Claims
Type Soundness: src/RFJ/Theorems/TypeSoundness.v

Logical Soundness: src/RFJ/Theorems/LogicalSoundness.v


## Requirements
Coq 8.17



## Acknowledgment
The initial development takes large inspiration from Michael H. Borkowski's mechanization on the local nameless representation, and from Pedro Abreu's coqfj the class definition and the Referable typeclass, to whom we are deeply grateful. The crush tactic is originally developed by Adam Chlipala. 


