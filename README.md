# fol-parser
A DSL written in Python for writing z3 rules a bit more comfortably.

## Brief showcase

The following code describes the first order theory of (connected) trees.
```
    Preamble
          Sort node.
          Function child: node, node -> B.
          Constant x, y, z: node.
          Constant a: node.
          Bound 10. 
  
      Logic
          All x: (~child(x, x)).
          All x, y, z: ((child(x, y), child(y, z)) => child(x, z)).
          All x, y, z: (child(x, z), child(y, z)) => (child(x, y) | child(y, x) | x = y).
          Some z: (All x, y: (child(z, x) | z = x), (child(z, y) | z = y)).
          
          All x: (x != a => child(a, x)).
  
      Query
          Models a.
```

The first line begins the preamble, in which all function and constant names must be declared,
as well as all sorts.

The following lines declare a new sort, *node*, and define
* the function *child* from pairs of nodes to booleans
* the constants *x*, *y*, *z* and *a*, which are separated just for clarity.

Also, the preamble defines the bound for the model checker, which will show only the first 10 models
it finds.

The Logic section adds rules for stating that the descendant relation is asymmetric and transitive,
that any two nodes that are predecessors of the same node either form a succesion or are the
same node, that the tree is connected, and that a special constant *a* is the root.

Finally, the Query section instructs Z3 to show the value of *a* in ten different models.

## Why a Z3 DSL?
Sometimes, once you have a sufficiently clear idea of how you want to model a domain,
it is easier to write a fully formal specification if the language you are using looks 
clean and has few visual distractions.

The SMT library syntax uses prefix notation, which at least for me adds some cognitive overhead.

Hence the style of this DSL.

## Fatal flaws
* So far the parsing library this DSL uses does not support precedence relations between
operators (so one has to write parentheses to avoid ambiguities, with the added ugliness
and errors), but I'm currently trying to fix this issue.
* No error reporting (you'll either get Lark's error reports, or a python error,
not something more carefully planned) as of yet.
* New and poorly tested (hopefully new features will be added, and bugs in those
that are already present will be fixed).

## What is Z3?
Z3 is a satisfiability modulo theory solver: it is a first order logic solver
(kinda like prolog, but for normal people) which also includes specialized
machinery for working with theories such as integer arithmetic, bitvectors, sequences,
and datatypes, and tricky relations like the transitive closure.

## What is it useful for?
It has been used for synthesizing programs, finding loop invariants
in imperative programs, model checking, and manu other applications.
It also includes specialized solvers for Horn clauses
(but these won't be available in this DSL).

## Short term ToDos
* Dump whole models to JSON files so users can do something useful with them.
* Fix errors arising when using arithmetic.
* Add support for datatypes.
* Add support for comments.

## Long term ToDos
* Define a sensible semantics for multi-variable model checking (stack pops might be useful).
