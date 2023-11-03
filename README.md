# pi4-isabelle
Isabelle/HOL formalization of Π4, a dependently-typed version of P4[1].
Project outside of course scope @ DIKU.

[1] Matthias Eichholz, Eric Hayden Campbell, Matthias Krebs, Nate Foster, and Mira Mezini. 2022. Dependently Typed Data
Plane Programming. Proc. ACM Program. Lang. 6, POPL, Article 40 (January 2022), 83 pages. https://doi.org/10.1145/3498701

## Structure

A brief overview over the theory files:
- `Syntax.thy` defines the main datastructures used to model the language.
  This includes the AST, the types, as well as auxiliary types to model e.g. type environments.
- `Utils.thy` defines various utility functions and auxiliar lemmas.
- `Semantics.thy` defines small-step operation semantics for the language, as well as denotational semantics for
   expressions and formulas.
- `Chomp.thy` defines the `chomp` and `heapRef_1` functions that are used to type the instance extraction command.
- `Types.thy` defines the main typing judgements, and gives various additional definitions relating to types, e.g. the
  subtyping relation.
- `Chomp_Correctness.thy` attempts to prove the correctness of the syntactic chomp operation.

## Progress

Defining all the relevant constructs took longer than hoped for; the main paper omits several definitions and others had
to be augmented to be suitable for formalization. As a consequence, I did not get all the way to proving the main theorems
of the paper in the scope of the project outside of course scope: Progress and Preservation, and therefore soundness of
the type system.

As of now, we have proofs for various auxiliary lemmas and a good chunk of the theorem showing correctness of the syntactic
chomp operation with respect to the semantic chomp operation. The lemmas used as stepping stones in this proof also
required a fair number of modifications over the original versions from the paper to actually be correct in all cases.
The proof also includes many subcases that are omitted in the paper; they are not as trivial as the paper assumes.