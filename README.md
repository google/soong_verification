# Formal verification of Android build code

## About
This project concerns the [Soong](https://android.googlesource.com/platform/build/soong/+/master/README.md) build system in Android. The work was done as part of a summer internship, and the best summary can be found in the following presentation ([slides w/ commentary](https://drive.google.com/file/d/176SGJ9zVR3mTy5Q1f7w0QcVQ0r9eetJv/view?usp=sharing), [video](https://drive.google.com/file/d/1_mq_Sg6wXxDOCYopIB8zq_FU9UwUZKlx/view?usp=sharing)), which also provides some general background on formal verification. This project is written using [Lean Theorem Prover](https://leanprover-community.github.io/). The section below also provides a brief overview.

## Overview

The Android build system is composed of many moving parts, incorporating multiple programming languages. There is no “ground truth” specification of the whole process; however, it’s necessary to have some mental model of how the build process works when contributing to this codebase, so this modeling will nevertheless be done, only informally and in varied ways by different engineers. Past bugs have arisen due to these inconsistencies.

This issue can be addressed by formalizing a model at a high level. For example, we could declare an entity called `Library_class` which characterizes how similar kinds of libraries that get built have similar properties (a certain degree of similarity can be assumed to hold between two libraries with the same library class):

```
inductive Library_class
 | system : Library_class
 | vendor : Library_class
 | product : Library_class
```

Furthermore, given some formalization of libraries themselves (e.g. libutils, libgui) in a `Library` data structure, we can declare that the build system ought to be able to look at any given library and determine which `Library_classes` it belongs to.

```
def assign_lib_classes: Library → finset Library_class :=
     <some concrete specification of how we think this should work>
```

One use for formal methods is to show our high level models are internally consistent. Consider the fact that we also believe that every `Library` belongs to *some* `Library_class`. We can formalize this by furnishing a proof that for every input, `assign_library_classes` returns a nonempty set.

```
theorem every_library_has_at_least_one_class:
  ∀ (lib: Library), (assign_lib_classes lib).nonempty :=
    <some proof>
```

A more involved use case of formal verification is to prove programs meet some specification. Suppose there were an analogous piece of Go code which correctly assigns a set of `Library_class` to a `Library`. We can construct models of Go programs within the proof assistant:

```
def assign_class_prog: Program := <construct the program>
```

In general there are many properties we could try to verify for a given `Program`, but in this case we can give a full specification because this program ought perform the same function as our high-level model function. To assert that the program terminates with the same value as the (given some trivial definitions for checking the output of a program and converting values in the high level model to values in our program model), the proof we want is:

```
theorem assign_class_prog_meets_specification:
∀ (lib: Library),
    check_input_output -- args: program, input, expected output
      assign_class_prog
      (Lib_to_Go lib)
      (LibClasses_to_Go (assign_lib_classes lib))
  := <some proof>
```

The most challenging part of this process is proving properties about our formal models of Go programs. This is the domain of [separation logic](https://en.wikipedia.org/wiki/Separation_logic), the (partially-completed) implementation of which makes up most of the code in this repo.

## Related work
There is a large literature for Hoare logic and separation logic based program verification. Among these, [this paper](https://staff.aist.go.jp/reynald.affeldt/documents/vtls-long.pdf) (2014) pretty prints verified C code from Coq and is the closest real-world example we’ve found to something that meets our needs. This [Coq](https://github.com/coq-community/hoare-tut) tutorial walks through a lot of the concepts involved with helpful code annotations.

[This](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.59.5332&rep=rep1&type=pdf) is a potentially-useful example of separation logic with classes and method calls.

## Project Structure
The code in `src` is structured by the following top-level directories.

- `pretty_printing/` defines a datatype capturing Go syntax and defines
    methods to print valid Go code.
    -   Examples are found in `/test_go_pp.lean`.

- `soong_model/` represents a higher abstraction of how the Soong build system works, and some en within that model will be connected to the above directories which focus on verfiying Go programs.

- `seplog/` models the Go code semantics with separation logic.
  - Partially modeled off of [this](https://github.com/affeldt-aist/seplog)

## Usage

-   This is best viewed using a Lean editor (e.g. VScode, Emacs)
    -   This requires an installation of Lean (3.16.5) on your machine
    -   Installation instructions [here](https://leanprover-community.github.io/install/linux.html)
-   This depends on `mathlib`, which must be specified in `leanpkg.path`.

## To do

- Instead of indexing fields/methods by strings, have a custom type for each structure (to prevent class of errors where we access a method that doesn’t exist)
- Introduce comments in Golang model (e.g. add a string field to “skip”)
- Forbid invalid names for fields, methods, structures, etc.
- Forbid duplicate name between receiver of a method and one of its arguments
- Remove `sorry` by translating Coq proofs into Lean proofs (if possible)
- Weakest precondition logic for the additional program constructors we added: `declare` and `new` (alternatively, implement these in terms of `malloc` and `free` which have definitions already)