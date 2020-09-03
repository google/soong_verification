# Formal verification of Android build code

## About
This project concerns the [Soong](https://android.googlesource.com/platform/build/soong/+/master/README.md) build system in Android. This work was done as part of a Google internship, the summarized in the following presentation ([slides w/ commentary](https://drive.google.com/file/d/176SGJ9zVR3mTy5Q1f7w0QcVQ0r9eetJv/view?usp=sharing), [video](https://drive.google.com/file/d/1_mq_Sg6wXxDOCYopIB8zq_FU9UwUZKlx/view?usp=sharing)).

## Bigger Picture

The Android build system is composed of many moving parts, incorporating multiple programming languages. There is no “ground truth” specification of the whole process; however, it’s necessary to have at least some mental model of how the build process works when contributing to this codebase, so this modeling will nevertheless be done, only informally and potentially varied ways by different engineers. Multiple past bugs have arisen due to inconsistencies within the codebase (examples).

This issue can be systematically addressed by formalizing a model at a high level. For example, we could declare an entity called `Library_class` (for simplicity, model it as taking one of three values):

```
inductive Library_class
 | system : Library_class
 | vendor : Library_class
 | product : Library_class
```

Furthermore, given some formalization of libraries themselves (e.g. libutils, libgui) in a `Library` data structure, we can declare that the build system ought to be able to look at any given library and determine which `Library_classes` it belongs to.

```
def assign_lib_classes: Library → list Library_class :=
<some concrete specification of how we think this should work>
```

Already we can gain value from formal methods at this stage because we also informally have the assumption that every `Library` belongs to some class. We can formalize this by furnishing a proof that for every input, `assign_library_classes` returns a nonempty list.

```
theorem every_library_has_at_least_one_class:
  ∀ (lib: Library), (assign_lib_classes lib).nonempty :=
<some proof>
```

Soong requires Go code which correctly performs this library class assignment. We can construct models of Go programs within the proof assistant:

```
def assign_class_prog: Program := <construct the program>
```

And, given some trivial definitions for check_input_output, `Lib_to_Go` and `Classlist_to_Go` functions, the proof we want is:

```
theorem assign_class_prog_meets_specification:
∀ (lib: Library),
 	check_input_output
assign_class_prog
(Lib_to_Go lib)
Classlist_to_Go (assign_lib_classes lib)
  := <some proof>
```

The most challenging part of this process is proving properties about our formal models of Go programs. This will be the focus of the remainder of the document.

## Related work
There is a large literature for Hoare logic and separation logic based program verification. Among these, this paper (2014) pretty prints verified C code from Coq and is the closest real-world example we’ve found so far to our plan. This Coq tutorial walks through a lot of the concepts involved with helpful code annotations.

This is a potentially-useful example of separation logic with classes and method calls.

## Project Structure
The code in `src` is structured by the following top-level directories.

- `pretty_printing/` defines a datatype capturing Go syntax and defines
    methods to print valid Go code.
    -   Examples are found in `/test_go_pp.lean`.

- `soong_model/` represents a higher abstraction of how the Soong build system works, and some functions within that model will be connected to the above directories which focus on verfiying Go programs.

- `seplog/` models the Go code semantics with separation logic.
  - Partially modeled off of [this](https://github.com/affeldt-aist/seplog)

## Usage

-   This is best viewed using a Lean editor (e.g. VScode, Emacs)
    -   This requires an installation of Lean (at least 3.17.1) on your machine
    -   Installation instructions [here](https://leanprover-community.github.io/install/linux.html)
-   This depends on `mathlib`, which must be specified in `leanpkg.path`.
