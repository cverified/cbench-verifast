The two proofs illustrate two ways to define concepts by recursion on 
int in VeriFast: using predicates (which have the upside of allowing 
arbitrary recursion in positive positions, and the downside of requiring 
explicit opening, closing, merging, and leaking in some cases) or using 
"fixpoint functions" (primitive recursive functions, which have the 
upside of enjoying automatic reduction if the inductive argument is a 
constructor and the downside of not supporting recursion on int directly 
and require conversion to nat for that).
