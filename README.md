# Boolean_Unification
This is an implementation of Boolean Unification in Haskell.
The is somewhat based of ["Embedding Boolean Expressions into Logic Programming"](https://core.ac.uk/download/pdf/82206645.pdf).

This unifier takes the algorithm from the paper and applies a simple heuristic to solve (for zero / for false) sets of problems in algebraic normal form.
The variable that appears in least number of problem is choosen to be solved for.
The problems are combined into a single problem using boolean logic then the method in from paper is applied.
This is appiled recursively until all varibales are solved.