# FLK-Semantics
Writing out small-step and big-step operational semantics for the FLK language in Idris

## FLK
FLK is a small functional language described in *Design Concepts in Programming
Languages* by Turbak and Gifford.

## Approach
There are definitions of small-step and big-step operational semantics given in
`FLK_sos` and `FLK_bos` respectively. They also include evaluators which carry
proofs that they conform to the given semantics (though the sos evaluator
currently has bugs).
