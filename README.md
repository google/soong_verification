# Formal verification of Android build code

## About
The [Soong](https://android.googlesource.com/platform/build/soong/+/master/README.md) Android build system offers a flexible configuration file format for Android developers, though this syntactically allows for undesirable build processes to be declared. Soong has a Go code base which checks for certain undesirable properties so that builds can fail safely (though it does this in an ad hoc way). My internship goal is to introduce formal methods into this build process - we want to specify a property and have confidence that Soong’s Go code will fail for build configurations which do not meet this specification. For this, we need proofs written in a Proof Assistant as well as a tight connection between these proofs and the production Go code.

This work was done as part of a Google internship, the final presentation of which can be found [here](https://drive.google.com/file/d/176SGJ9zVR3mTy5Q1f7w0QcVQ0r9eetJv/view?usp=sharing) (video recording [here](https://drive.google.com/file/d/1_mq_Sg6wXxDOCYopIB8zq_FU9UwUZKlx/view?usp=sharing)).

## Structure
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
