# Algebras for a functor - Student project

## Content

The project extends the built in `F-Algebra` and `F-Algebra-Morphism` structures.
It shows that they form a category and implements the following:

* `F-algebra-category` : the category consisting of F-algebras and
  F-algebra morphisms

* `polynomial-functor` : a special case of functors

* `Nat-algebra-initial` : proof that natural numbers can be represented with 
  the help of F-algebras and polynomial functors

* `polynomial-initial` : the existence of initial algebras for F-algebra categories 
  for polynomial functors

* `lambek-lemma` : the Lambek lemma

## Project structure

This repository is set up as an Agda library and it contains:

* `lograc-project.agda-lib`: the library configuration file which contains
  the list of file system paths that Agda should include

* `agda-stdlib/`: Agda standard library as a git submodule

* `agda-categories/`: Agda categories library as a git submodule

* `project/`: the top-level source code directory for your Agda code
