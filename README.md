# Inferno Example

This repo contains the example code from François Pottier's ICFP '14 Functional Pearl "Hindley-Milner Elaboration in Applicative Style", which describes the design of the type inference library Inferno.
Specifically, this repo contains the code from Section 5 of the paper, in which 
an untyped ML calculus is elaborated to System F. 

This code in this repo is taken from [François Pottier's Inferno codebase](https://gitlab.inria.fr/fpottier/inferno/-/tree/master?ref_type=heads) on GitLab. 

## Running tests 

- Tests for type-checking System F terms: `dune exec -- test/TestF.exe`
- Tests for ML programs: `dune exec -- test/TestML.exe`

## Running the midml program
`midml.ML` is a very simple frontend program that parses, infers and
type-checks a source file in the "mid-ML" language in this repo. 

Run this program using:
```ocaml
dune exec -- midml foo.midml
```



