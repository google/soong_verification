# Formal verification of Android build code

## About

The code is structured by the following top-level directories.

-   `pretty_printing/` defines a datatype capturing Go syntax and defines
    methods to print valid Go code.

    -   Examples are found in `/test_go_pp.lean`.

- `soong_model/` represents a higher abstraction of how the Soong build system
  works, and some functions within that model will be connected to the above
  directories which focus on verfiying Go programs.

- `seplog/` models the Go code semantics with separation logic.
  - Partially modeled off of [this](https://github.com/affeldt-aist/seplog)

## Usage

-   This is best viewed using a Lean editor (e.g. VScode, Emacs)
    -   This requires an installation of Lean (at least 3.17.1) on your machine
    -   Installation instructions
        [here](https://leanprover-community.github.io/install/linux.html)
-   This depends on `mathlib`, which must be specified in `leanpkg.path`.
